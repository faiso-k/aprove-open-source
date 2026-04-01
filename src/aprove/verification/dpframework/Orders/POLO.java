package aprove.verification.dpframework.Orders;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;

/**
 * Represents a polynomial ordering on natural numbers
 * based upon a given polynomial interpretation
 * of function symbols.
 *
 * @author Andreas Capellmann, Carsten Fuhs
 */
public class POLO implements QActiveOrder, PartiallyMonotonicOrder {

    final static String orderName = "polynomial order";

    //public Afs implicitAfs;

    private final Interpretation interpretation;

    private POLO(final Interpretation interpretation) {
        //this.implicitAfs = null;
        this.interpretation = interpretation;
    }

    /**
     * Create a new polynomial ordering based on a polynomial interpretation.
     *
     * @param interpretation
     *            polynomial interpretation of function symbols
     */
    public static POLO create(final Interpretation interpretation) {
        return new POLO(interpretation);
    }

    /**
     * @return the interpretation on which this is based
     */
    public Interpretation getInterpretation() {
        return this.interpretation;
    }

    /**
     * Returns whether Pol(t1) > Pol(t2) according to the used interpretation
     * of function symbols.
     *
     * @param t1 first term
     * @param t2 second term
     * @return whether Pol(t1) > Pol(t2) holds given the current
     *  interpretation for function symbols
     */
    @Override
    public boolean inRelation(final TRSTerm t1, final TRSTerm t2) {
        VarPolynomial p1 = null;
        VarPolynomial p2 = null;
        try {
            // XXX - real abortion
            p1 = this.interpretation.interpretTerm(t1, AbortionFactory.create());
            p2 = this.interpretation.interpretTerm(t2, AbortionFactory.create());
            final VarPolynomial pDiff = p1.minus(p2);
            VarPolyConstraint pDiffConstraint;
            pDiffConstraint = new VarPolyConstraint(pDiff, ConstraintType.GT);
            return pDiffConstraint.isValid();
        } catch (final AbortionException e) {
        }
        return false;
    }

    /**
     * Checks whether this solves <code>c</code>.
     *
     * @param c the term constraint to check
     * @return <code>true</code> if constraint lies in the polynomial
     *         ordering, <code>false</code> otherwise
     */
    @Override
    public boolean solves(final Constraint<TRSTerm> c) {
        VarPolynomial p1 = null, p2 = null, pDiff;
        try {
            // XXX - real abortion
            p1 = this.interpretation.interpretTerm(c.getLeft(), AbortionFactory.create());
            p2 = this.interpretation.interpretTerm(c.getRight(), AbortionFactory.create());
            pDiff = p1.minus(p2);
            final OrderRelation rel = c.getType();
            ConstraintType type;
            switch (rel) {
            case EQ:
                type = ConstraintType.EQ;
                break;
            case GE:
                type = ConstraintType.GE;
                break;
            case GR:
                type = ConstraintType.GT;
                break;
            default:
                throw new RuntimeException("POLO cannot handle constraint type " + rel + " !");
            }
            VarPolyConstraint pDiffConstraint;
            pDiffConstraint = new VarPolyConstraint(pDiff, type);
            return pDiffConstraint.isValid();
        } catch (final AbortionException e) {
        }
        return false;
    }

    /**
     * Checks whether Pol(t1) = Pol(t2) in the polynomial interpretation on
     * which this is based.
     *
     * @param t1 first term
     * @param t2 second term
     * @return whether Pol(t1) = Pol(t2) in the underlying polynomial
     *  interpretation of this
     */
    @Override
    public boolean areEquivalent(final TRSTerm t1, final TRSTerm t2) {
        VarPolynomial p1 = null;
        VarPolynomial p2 = null;
        try {
            // XXX - real abortion.
            p1 = this.interpretation.interpretTerm(t1, AbortionFactory.create());
            p2 = this.interpretation.interpretTerm(t2, AbortionFactory.create());
            final VarPolynomial pDiff = p2.minus(p1);
            VarPolyConstraint pDiffConstraint;
            pDiffConstraint = new VarPolyConstraint(pDiff, ConstraintType.EQ);
            return pDiffConstraint.isValid();

        } catch (final AbortionException e) {
        }
        return false;
    }

    /**
     * Returns the string representation of this polynomial ordering.
     */
    @Override
    public String toString() {
        return this.interpretation.toString();
    }

    @Override
    public String export(final Export_Util eu) {
        return this.interpretation.export(eu);
    }

    @Override
    public boolean checkQActiveCondition(final QActiveCondition condition) {
        final SimplePolynomial activePoly = this.interpretation.getActiveConstraint(condition);
        final boolean result = activePoly == SimplePolynomial.ONE;
        if (Globals.useAssertions) {
            if (!result) {
                // why did we choose to compare by "==" in the first place?
                assert activePoly.getNumericalAddend().signum() <= 0;
            }
        }
        return result;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        return this.interpretation.toCPF(doc, xmlMetaData);
    }

    @Override
    public String isCPFSupported() {
        return null;
    }

    @Override
    public boolean fIsMonotonicInArg(final FunctionSymbol f, final int i) {
        return this.interpretation.isMonotonicIn(f, i);
    }
}
