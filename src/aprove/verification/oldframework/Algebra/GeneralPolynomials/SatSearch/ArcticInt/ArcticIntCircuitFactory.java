package aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.ArcticInt;

import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * A CircuitFactory for constraints over (positive) arctic integers.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class ArcticIntCircuitFactory extends ExoticIntCircuitFactory<ArcticInt> {

    private static final boolean minimalisticGT = true;

    // true:  max(x,y) :=  x >  y ? x : y
    // false: max(x,y) :=  x >= y ? x : y
    private static final boolean useGTforPlus = true;

    public ArcticIntCircuitFactory(
            final FormulaFactory<None> formulaFactory) {
        super(formulaFactory);
    }

    @Override
    public Formula<None> buildGTCircuit(
            final List<? extends Formula<None>> xs,
            final List<? extends Formula<None>> ys) {
        Formula<None> xFlag = xs.get(0);
        Formula<None> yFlag = ys.get(0);
        if (ArcticIntCircuitFactory.minimalisticGT) {
            Formula<None> xIsGreater = this.natCircuitFactory.buildGTCircuit(
                    xs.subList(1, xs.size()), ys.subList(1, ys.size()));
            return this.formulaFactory.buildOr(yFlag,
                    this.formulaFactory.buildAnd(this.formulaFactory.buildNot(xFlag),
                            xIsGreater));

        } else {
            Formula<None> bothNegInf = this.formulaFactory.buildAnd(xFlag, yFlag);
            Formula<None> xIsGreater = this.natCircuitFactory.buildGTCircuit(
                    xs.subList(1, xs.size()), ys.subList(1, ys.size()));
            return this.formulaFactory.buildOr(bothNegInf,
                    this.formulaFactory.buildAnd(this.formulaFactory.buildNot(xFlag),
                            this.formulaFactory.buildOr(yFlag, xIsGreater)));
        }
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

        // The maximum function is encoded by comparing xs and ys
        // and setting the result's bits accordingly. The comparison
        // formula should only be evaluated once by the SAT solver,
        // making this method quite efficient (not to mention simple).
        Formula<None> xsIsResult;
        if (ArcticIntCircuitFactory.useGTforPlus) {
            xsIsResult = this.buildGTCircuit(xfs, yfs);
        } else {
            xsIsResult = this.buildGECircuit(xfs, yfs).x;
        }


        int length = Math.max(xfs.size(), yfs.size());
        Formula<None> zero = this.formulaFactory.buildConstant(false);
        List<Formula<None>> zs = new ArrayList<Formula<None>>(length);
        zs.add(this.formulaFactory.buildAnd(xfs.get(0), yfs.get(0))); // neginf flag
        for (int i = 1; i < length; i++) {
            Formula<None> xi = i < xfs.size() ? xfs.get(i) : zero;
            Formula<None> yi = i < yfs.size() ? yfs.get(i) : zero;
            zs.add(this.formulaFactory.buildIte(xsIsResult, xi, yi));
        }

        return new PolyCircuit(zs, xs.getMax().max(ys.getMax()));
    }
}
