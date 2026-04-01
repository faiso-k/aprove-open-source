package aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.ArcticInt;

import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A CircuitFactory for constraints over (positive) tropical integers.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class TropicalIntCircuitFactory extends ExoticIntCircuitFactory<ArcticInt> {

    public TropicalIntCircuitFactory(
            final FormulaFactory<None> formulaFactory) {
        super(formulaFactory);
    }

    @Override
    public Formula<None> buildGTCircuit(
            final List<? extends Formula<None>> xs,
            final List<? extends Formula<None>> ys) {
        Formula<None> xFlag = xs.get(0);
        Formula<None> yFlag = ys.get(0);
        Formula<None> bothFinite = this.formulaFactory.buildAnd(
                this.formulaFactory.buildNot(xFlag),
                this.formulaFactory.buildNot(yFlag));

        // xs > ys iff xs is infinite or ys is finite and smaller than xs
        Formula<None> xIsGreater = this.natCircuitFactory.buildGTCircuit(
                xs.subList(1, xs.size()), ys.subList(1, ys.size()));

        return this.formulaFactory.buildOr(xFlag,
                this.formulaFactory.buildAnd(bothFinite, xIsGreater));
    }

    @Override
    public Pair<Formula<None>, Formula<None>> buildGECircuit(
            final List<? extends Formula<None>> xs,
            final List<? extends Formula<None>> ys) {
        Formula<None> xFlag = xs.get(0);
        Formula<None> yFlag = ys.get(0);
        Formula<None> bothFinite = this.formulaFactory.buildAnd(
                this.formulaFactory.buildNot(xFlag),
                this.formulaFactory.buildNot(yFlag));

        // xs >= ys iff xs is infinite or ys is finite and <= xs
        Formula<None> xGEyFinite = this.natCircuitFactory.buildGECircuit(
                xs.subList(1, xs.size()), ys.subList(1, ys.size())).x;

        Formula<None> xEQy = this.buildEQCircuit(xs, ys);

        Formula<None> xGEy = this.formulaFactory.buildOr(xFlag,
                this.formulaFactory.buildAnd(bothFinite, xGEyFinite));

        return new Pair<Formula<None>, Formula<None>>(xGEy, xEQy);
    }


    /**
     * Build a circuit that encodes `min(xs, ys)` (tropical addition).
     * @param xs A list of propositional formulae encoding a
     * tropical integer (variable or number).
     * @param ys Ditto.
     */
    @Override
    public PolyCircuit buildPlusCircuit(final PolyCircuit xs, final PolyCircuit ys) {

        List<Formula<None>> xfs = xs.getFormulae();
        List<Formula<None>> yfs = ys.getFormulae();

        // The minimum function is encoded by comparing xs and ys
        // and setting the result's bits accordingly. The comparison
        // formula should only be evaluated once by the SAT solver,
        // making this method quite efficient (not to mention simple).
        Formula<None> xsIsLessOrEqual = this.buildGTCircuit(yfs, xfs);

        int length = Math.max(xfs.size(), yfs.size());
        Formula<None> zero = this.formulaFactory.buildConstant(false);
        List<Formula<None>> zs = new ArrayList<Formula<None>>(length);
        zs.add(this.formulaFactory.buildAnd(xfs.get(0), yfs.get(0))); // infinity flag
        for (int i = 1; i < length; i++) {
            Formula<None> xi = i < xfs.size() ? xfs.get(i) : zero;
            Formula<None> yi = i < yfs.size() ? yfs.get(i) : zero;
            zs.add(this.formulaFactory.buildIte(xsIsLessOrEqual, xi, yi));
        }

        return new PolyCircuit(zs, xs.getMax().min(ys.getMax()));
    }
}
