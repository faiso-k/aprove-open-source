/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints.idp;

import java.math.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

public class InfRulePolyGcd extends InfRuleConstraintRepl<Object> {

    public InfRulePolyGcd() {
        super(Mode.Full);
    }

    @Override
    public InfRuleID getID() {
        return InfRuleID.IDP_POLY_GCD;
    }

    @Override
    public String getLongName() {
        return "Rule IDP_POLY_GCD: divide polynomials by gcd";
    }

    @Override
    public String getName() {
        return "IDP_POLY_GCD";
    }

    @Override
    protected Constraint processConstraint(
        final Implication origImplication,
        Constraint constraint,
        final boolean isConclusion,
        final Object data,
        final Abortion aborter) throws AbortionException
    {
        if (constraint.isPolyAtom()) {
            if (constraint.getTag(this.getID()) != null) {
                return constraint;
            }
            constraint.setTag(this.getID(), Boolean.TRUE);
            final PolyAtom<BigIntImmutable> atom = (PolyAtom<BigIntImmutable>) constraint;
            final IDPGInterpretation interpretation = (IDPGInterpretation) this.getIrc().getPolyInterpretation();
            final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> lhs = atom.getLhs();
            interpretation.getFvOuter().applyTo(lhs);
            BigInteger gcd = null;
            for (final Map.Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> monomial : lhs.getMonomials(
                interpretation.getOuterRingMonoid()).entrySet())
            {
                interpretation.getFvInner().applyTo(monomial.getValue());
                if (monomial.getValue().isConstant()) {
                    final BigInteger constant =
                        monomial.getValue().getConstantPart(interpretation.getInnerRingMonoid()).getBigInt().abs();
                    if (!constant.equals(BigInteger.ZERO)) {
                        if (gcd == null) {
                            gcd = constant;
                        } else {
                            gcd = constant.gcd(gcd);
                        }
                    }
                } else {
                    return constraint;
                }
            }
            if (gcd != null && !gcd.equals(BigInteger.ONE)) {
                // System.err.println("GCD " + gcd);
                GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> newLhs = null;
                final GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> fact =
                    interpretation.getFactory().getFactory();
                final GPolyFactory<BigIntImmutable, GPolyVar> innerFact = interpretation.getFactory().getInnerFactory();
                for (final Map.Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> monomial : lhs
                    .getMonomials(interpretation.getOuterRingMonoid())
                    .entrySet())
                {
                    final Collection<GPolyVar> vars = new ArrayList<GPolyVar>();
                    for (final Map.Entry<GPolyVar, BigInteger> varEntry : monomial.getKey().getExponents().entrySet()) {
                        for (int i = varEntry.getValue().intValue() - 1; i >= 0; i--) {
                            vars.add(varEntry.getKey());
                        }
                    }
                    final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> monPoly =
                        fact.concat(
                            innerFact.buildFromCoeff(BigIntImmutable.create(monomial
                                .getValue()
                                .getConstantPart(interpretation.getInnerRingMonoid())
                                .getBigInt()
                                .divide(gcd))),
                            fact.buildVariables(vars));
                    if (newLhs == null) {
                        newLhs = monPoly;
                    } else {
                        newLhs = fact.plus(newLhs, monPoly);
                    }
                }
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
                return constraint;
            }
        } else {
            // nothing to do
            return constraint;
        }
    }

    @Override
    protected Object prepare(final Implication implication, final Abortion aborter) {
        return null;
    }

}
