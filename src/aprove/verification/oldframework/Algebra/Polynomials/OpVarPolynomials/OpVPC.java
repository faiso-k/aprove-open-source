package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials;

import static aprove.verification.oldframework.Algebra.Polynomials.ConstraintType.*;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * An OpVPC (OpVarPolyConstraint) encodes two OpVarPolynomials in some relation
 * with each other where the relation is one of { =, >=, > }.
 *
 * @author fuhs
 * @version $Id$
 */
public class OpVPC {

    private final OpVarPolynomial lhs;
    private final OpVarPolynomial rhs;
    private final ConstraintType type;

    /**
     * @param lhs - non-null
     * @param rhs - non-null
     * @param type - non-null
     */
    public OpVPC(OpVarPolynomial lhs, OpVarPolynomial rhs, ConstraintType type) {
        if (Globals.useAssertions) {
            assert lhs != null;
            assert rhs != null;
            assert type != null;
        }
        this.lhs = lhs;
        this.rhs = rhs;
        this.type = type;
    }

    /**
     * Performing a case analysis, converts this to a set of CondVPCs.
     *
     * @param substitutor
     * @return
     */
    public Set<CondVPC> toCondVPCs(VPSubstitutor substitutor) {
        Set<CondVPC> result = new LinkedHashSet<CondVPC>();
        this.collectCondVPCs(substitutor, result, result, true);
        return result;
    }

    /**
     * Performing a case analysis, converts this to two set of CondVPCs.
     *
     * @param substitutor
     * @return
     *  x: the ">="-constraints that we get from p EQ q<br>
     *  y: the "<="-constraints that we get from p EQ q
     */
    public Pair<Set<CondVPC>, Set<CondVPC>> toCondVPCsPair(VPSubstitutor substitutor) {
        return this.toCondVPCsPair(substitutor, true);
    }


    /**
     * Performing a case analysis, converts this to two set of CondVPCs.
     *
     * @param substitutor
     * @param simplifyWithConclusion - allow simplifications involving
     *  the conclusion? Not recommandable if you intend to derive this.
     * @return
     *  x: the ">="-constraints that we get from p EQ q<br>
     *  y: the "<="-constraints that we get from p EQ q
     */
    public Pair<Set<CondVPC>, Set<CondVPC>> toCondVPCsPair(VPSubstitutor substitutor,
            boolean simplifyWithConclusion) {
        Set<CondVPC> resX = new LinkedHashSet<CondVPC>();
        Set<CondVPC> resY = new LinkedHashSet<CondVPC>();
        this.collectCondVPCs(substitutor, resX, resY, simplifyWithConclusion);
        Pair<Set<CondVPC>, Set<CondVPC>> res = new Pair<Set<CondVPC>, Set<CondVPC>>(resX, resY);
        return res;
    }


    /**
     * Via a case analysis for max and min, collects CondVPCs that correspond
     * to this.
     *
     * @param substitutor
     * @param geOrGtConstraints - will contain the ">="-constraints that we get from p EQ q
     * @param leOrLtConstraints - will contain the "<="-constraints that we get from p EQ q
     * @param simplifyWithConclusion - allow simplifications involving
     *  the conclusion? Not recommandable if you intend to derive this.
     */
    private void collectCondVPCs(VPSubstitutor substitutor,
            Set<CondVPC> geOrGtConstraints, Set<CondVPC> leOrLtConstraints,
            boolean simplifyWithConclusion) {
        // * get the CondVPs for the lhs and the rhs
        List<CondVarPolynomial> condLhs, condRhs;
        condLhs = this.lhs.getCondVPs(substitutor);
        condRhs = this.rhs.getCondVPs(substitutor);

        //int size = condLhs.size() * (this.type == ConstraintType.EQ ? condRhs.size() * 2 : condRhs.size());
        //Set<CondVPC> result = new LinkedHashSet<CondVPC>(size);

        // * then combine all the (sensible, i.e., not obviously inconsistent)
        //   conditions from both CondVPs and thus get the resulting constraint
        for (CondVarPolynomial cvpLhs : condLhs) {
            for (CondVarPolynomial cvpRhs : condRhs) {
                // check: can any inconsistencies be found in the
                // conditions that we get here?
                // if so, we ignore any constraint that would result since
                // (false /\ _ => _) always holds
                if (! cvpLhs.checkCondsForInconsistency(cvpRhs)) {
                    List<CondVarPolynomial> cvpsOfBothSides = new ArrayList<CondVarPolynomial>(2);
                    cvpsOfBothSides.add(cvpLhs);
                    cvpsOfBothSides.add(cvpRhs);

                    // now for the last condition. here we need to compare
                    // the values of cvpLhs and cvpRhs.
                    VarPolynomial lhsValue, rhsValue;
                    lhsValue = cvpLhs.getPoly();
                    rhsValue = cvpRhs.getPoly();

                    ConstraintType cType;
                    if (this.type == ConstraintType.GT) {
                        rhsValue = rhsValue.plus(VarPolynomial.ONE);
                        cType = ConstraintType.GE;
                    }
                    else {
                        cType = this.type;
                    }

                    switch (cType) {
                    case GE: {
                        VarPolyConstraint vpCondLhsGERhs = new VarPolyConstraint(lhsValue.minus(rhsValue), GE);

                        // check whether the conclusion of this new conditional
                        // constraint is valid on its own
                        // ( _ => TRUE always holds) or at least among its
                        // conditions/premises ( _ /\ foo => foo always holds)
                        if (! simplifyWithConclusion ||
                               ((! vpCondLhsGERhs.isValid()) &&
                                (! cvpLhs.conditionsEntail(vpCondLhsGERhs)) &&
                                (! cvpRhs.conditionsEntail(vpCondLhsGERhs)))) {
                            CondVPC cvpLhsGERhs = new CondVPC(cvpsOfBothSides, vpCondLhsGERhs);
                            geOrGtConstraints.add(cvpLhsGERhs);
                        }
                        break;
                    }
                    case EQ: {
                        VarPolyConstraint vpCondLhsGERhs = new VarPolyConstraint(lhsValue.minus(rhsValue), GE);
                        if (! simplifyWithConclusion ||
                               ((! vpCondLhsGERhs.isValid()) &&
                                (! cvpLhs.conditionsEntail(vpCondLhsGERhs)) &&
                                (! cvpRhs.conditionsEntail(vpCondLhsGERhs)))) {
                            CondVPC cvpLhsGERhs = new CondVPC(cvpsOfBothSides, vpCondLhsGERhs);
                            geOrGtConstraints.add(cvpLhsGERhs);
                        }
                        VarPolyConstraint vpCondRhsGELhs = new VarPolyConstraint(vpCondLhsGERhs.getPolynomial().negate(), GE);
                        if (! simplifyWithConclusion ||
                               ((! vpCondRhsGELhs.isValid()) &&
                                (! cvpLhs.conditionsEntail(vpCondRhsGELhs)) &&
                                (! cvpRhs.conditionsEntail(vpCondRhsGELhs)))) {
                            CondVPC cvpRhsGElhs = new CondVPC(cvpsOfBothSides, vpCondRhsGELhs);
                            leOrLtConstraints.add(cvpRhsGElhs);
                        }
                        break;
                    }
                    default:
                        throw new RuntimeException("Unexpected constraint type " + cType + "!");
                    }
                }
            }
        }
        //return geOrGtConstraints;
    }

    /**
     * Returns a set of CondVPCs that correspond to the derivative of
     * both sides of this wrt x (at those positions where the sides
     * of this is differentiable). This is accomplished by first
     * transforming this to CondVPCs and then taking the derivative
     * wrt x.
     *
     * @param x - a variable
     * @return a set of CondVPCs that correspond to the derivative of
     *  both sides of this wrt x (at those positions where the sides
     *  of this are differentiable)
     */
    public Set<CondVPC> deriveWRT(String x) {
        VPSubstitutor vps = new VPSubstitutor();
        Set<CondVPC> nonDerivedCondVPCs = this.toCondVPCs(vps);
        Set<CondVPC> result = new LinkedHashSet<CondVPC>();
        for (CondVPC condVPC : nonDerivedCondVPCs) {
            CondVPC derivative = condVPC.deriveWRT(x);

            // simple validity check, partial derivation
            // can simplify a constraint a lot
            if (! derivative.getConstraint().isValid()) {
                result.add(derivative);
            }
        }
        return result;
    }

    @Override
    public String toString() {
        return this.lhs + " " + this.type + " " + this.rhs;
    }

    @Override
    public int hashCode() {
        return this.lhs.hashCode() + 127*this.rhs.hashCode() + 449*this.type.hashCode();
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof OpVPC)) {
            return false;
        }
        OpVPC that = (OpVPC) o;
        return this.type.equals(that.type) && this.lhs.equals(that.lhs) && this.rhs.equals(that.rhs);
    }

    /**
     * @return Returns the lhs.
     */
    public OpVarPolynomial getLhs() {
        return this.lhs;
    }

    /**
     * @return Returns the rhs.
     */
    public OpVarPolynomial getRhs() {
        return this.rhs;
    }

    /**
     * @return Returns the type.
     */
    public ConstraintType getType() {
        return this.type;
    }
}
