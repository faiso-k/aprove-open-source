package aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.ArcticInt;

import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * A CircuitFactory for unary encoding of constraints over (positive) arctic integers.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class ArcticIntUnaryCircuitFactory extends ExoticIntUnaryCircuitFactory<ArcticInt> {

    // true:  for the finite part demand only that there exists a bit which is
    //        set on the greater bitvector and unset on the smaller bitvector
    // false: use the same encoding as for binary comparison
    private static final boolean minimalisticUnaryGT = false;

    public ArcticIntUnaryCircuitFactory(
            final FormulaFactory<None> formulaFactory) {
        super(formulaFactory);
    }

    @Override
    public Formula<None> buildGTCircuit(
            final List<? extends Formula<None>> xs,
            final List<? extends Formula<None>> ys) {
        int xsSize = xs.size();
        int ysSize = ys.size();
        int maxSize = Math.max(xsSize, ysSize);

        Formula<None> xInfinite = xs.get(0);
        Formula<None> yInfinite = ys.get(0);

        Formula<None> xIsGreater = null;
        Formula<None> zero = this.formulaFactory.buildConstant(false);
        if (ArcticIntUnaryCircuitFactory.minimalisticUnaryGT) {
            List<Formula<None>> somewhereGreater = new ArrayList<Formula<None>>(maxSize);
            for (int i = 1; i < maxSize; i++) {
                Formula<None> xi = i >= xsSize ? zero : xs.get(i);
                Formula<None> yi = i >= ysSize ? zero : ys.get(i);
                Formula<None> newTerm = this.formulaFactory.buildAnd(xi,
                        this.formulaFactory.buildNot(yi));
                somewhereGreater.add(newTerm);
            }
            xIsGreater = this.formulaFactory.buildOr(somewhereGreater);
        } else {
            for (int i = 1; i < maxSize; i++) {
                Formula<None> xi = i >= xsSize ? zero : xs.get(i);
                Formula<None> yi = i >= ysSize ? zero : ys.get(i);
                Formula<None> newTerm = this.formulaFactory.buildAnd(xi,
                        this.formulaFactory.buildNot(yi));
                if (xIsGreater == null) {
                    xIsGreater = newTerm;
                } else {
                    Formula<None> equality = this.formulaFactory.buildIff(xi, yi);
                    xIsGreater = this.formulaFactory.buildOr(newTerm,
                            this.formulaFactory.buildAnd(equality, xIsGreater));
                }
            }
        }
        return this.formulaFactory.buildOr(yInfinite,
                this.formulaFactory.buildAnd(
                        this.formulaFactory.buildNot(xInfinite), xIsGreater));
    }

    /**
     * Build a circuit that encodes `max(xs, ys)` (arctic addition).
     * @param xs A list of propositional formulae encoding an
     * arctic integer (variable or number).
     * @param ys Ditto.
     */
    @Override
    public PolyCircuit buildPlusCircuit(final PolyCircuit xs, final PolyCircuit ys) {

        List<Formula<None>> xfs = xs.getFormulae();
        List<Formula<None>> yfs = ys.getFormulae();

        int xfsSize = xfs.size();
        int yfsSize = yfs.size();

        int length = Math.max(xfsSize, yfsSize);
        Formula<None> zero = this.formulaFactory.buildConstant(false);
        List<Formula<None>> zs = new ArrayList<Formula<None>>(length);
        Formula<None> zIsInfinite = this.formulaFactory.buildAnd(xfs.get(0), yfs.get(0));
        zs.add(zIsInfinite); // neginf flag
        Formula<None> zIsFinite = this.formulaFactory.buildNot(zIsInfinite);
        Formula<None> oldZi = null;
        for (int i = 1; i < length; i++) {
            Formula<None> xi = i < xfsSize ? xfs.get(i) : zero;
            Formula<None> yi = i < yfsSize ? yfs.get(i) : zero;
            Formula<None> newZi;
            if (ExoticIntUnarizer.singleInfFlagImplication) {
                newZi = this.formulaFactory.buildOr(xi, yi);
                if (i == 1) {
                    this.unarizer.addGlobalConstraint(this.formulaFactory.buildImplication(newZi, zIsFinite));
                }
                zs.add(newZi);
            } else {
                newZi = this.formulaFactory.buildAnd(zIsFinite,
                            this.formulaFactory.buildOr(xi, yi));
                zs.add(newZi);
            }
            if (ExoticIntUnaryCircuitFactory.requirePrefixForPlus) {
                if (oldZi != null) {
                    Formula<None> prefixCond =
                        this.formulaFactory.buildImplication(newZi, oldZi);
                    this.unarizer.addGlobalConstraint(prefixCond);
                }
                oldZi = newZi;
            }
        }

        return new PolyCircuit(zs, xs.getMax().max(ys.getMax()));
    }
}
