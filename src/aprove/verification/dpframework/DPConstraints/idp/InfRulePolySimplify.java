/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints.idp;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

public class InfRulePolySimplify extends InfRuleConstraintRepl<Object> {

    public InfRulePolySimplify() {
        super(Mode.Full);
    }

    @Override
    public InfRuleID getID() {
        return InfRuleID.IDP_POLY_SIMPLIFY;
    }

    @Override
    public String getLongName() {
        return "Rule IDP_POLY_SIMPLIFY: simplify polynomial";
    }

    @Override
    public String getName() {
        return "IDP_POLY_SIMPLIFY";
    }

    @Override
    protected Constraint processConstraint(
        Implication origImplication,
        Constraint constraint,
        boolean isConclusion,
        Object data,
        Abortion aborter) throws AbortionException
    {
        if (constraint.isPolyAtom()) {
            if (constraint.getTag(this.getID()) != null) {
                return constraint;
            }
            constraint.setTag(this.getID(), Boolean.TRUE);
            PolyAtom<BigIntImmutable> atom = (PolyAtom<BigIntImmutable>) constraint;
            IDPGInterpretation interpretation = (IDPGInterpretation) this.getIrc().getPolyInterpretation();
            GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> newLhs =
                GPolySimplifyer.simplify(
                    atom.getLhs(),
                    interpretation.getFvInner(),
                    interpretation.getFvOuter(),
                    interpretation.getFactory().getFactory());
            if (newLhs != atom.getLhs()) {
                constraint =
                    PolyAtom.create(
                        newLhs,
                        atom.getRelation(),
                        interpretation,
                        atom.getTermAtom(),
                        atom.getLeft(),
                        atom.getRight(),
                        atom.getRecommendation());
                constraint.setTag(this.getID(), Boolean.TRUE);
                return constraint;
            } else {
                return atom;
            }
        } else {
            // nothing to do
            return constraint;
        }
    }

    @Override
    protected Object prepare(Implication implication, Abortion aborter) {
        return null;
    }

}
