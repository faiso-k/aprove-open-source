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
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Docu-guess (fuhs):
 * This rule applies the famous absolute positiveness criterion (Hong, Jakus)
 * to eliminate universally quantified variables:
 *
 * * If x, y range over N, then a*x + b*y + c >= 0 becomes
 *   a >= 0 and b >= 0 and c >= 0.
 *
 * * If x, y range over Z, then a*x + b*y + c >= 0 becomes
 *   a = 0 and b = 0 and c >= 0.
 */
public class InfRuleUnboundedVars extends InfRule {

    @Override
    public Pair<Constraint, InfProofStepInfo> applyToImplication(final Implication implication, final Abortion aborter)
        throws AbortionException
    {
        final Set<GPolyVar> unboundedVars = new LinkedHashSet<GPolyVar>(implication.getConclusion().getPolyVariables());
        unboundedVars.removeAll(implication.getConditions().getPolyVariables());
        if (unboundedVars.isEmpty()) {
            return new Pair<Constraint, InfProofStepInfo>(implication, null);
        }
        Set<Constraint> conclusions;
        if (implication.getConclusion().isConstraintSet()) {
            conclusions = (ConstraintSet) implication.getConclusion();
        } else {
            conclusions = Collections.singleton(implication.getConclusion());
        }
        final IDPGInterpretation interpretation = (IDPGInterpretation) this.getIrc().getPolyInterpretation();
        final ConstraintType varCoeffConstraintType = interpretation.isNat() ? ConstraintType.GE : ConstraintType.EQ;
        final GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> factory =
            interpretation.getFactory().getFactory();
        final Set<Constraint> newConclusions = new LinkedHashSet<>();
        boolean changed = false;
        for (final Constraint conclusion : conclusions) {
            if (conclusion.isPolyAtom()) {
                final PolyAtom<BigIntImmutable> atom = (PolyAtom<BigIntImmutable>) conclusion;
                final Set<GPolyVar> atomUnbounded = new LinkedHashSet<>(atom.getPolyVariables());
                atomUnbounded.retainAll(unboundedVars);
                if (atomUnbounded.isEmpty()) {
                    newConclusions.add(conclusion);
                    continue;
                }
                if (!atom.getLhs().isFlat(interpretation.getOuterRingMonoid())) {
                    interpretation.getFvOuter().applyTo(atom.getLhs());
                }
                GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> sum = null;
                boolean atomChanged = false;
                for (final Map.Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> monomial : atom
                    .getLhs()
                    .getMonomials(interpretation.getOuterRingMonoid())
                    .entrySet())
                {
                    final Collection<GPolyVar> vars = new ArrayList<GPolyVar>();

                    // docu-guess (fuhs):
                    // a monomial is called /restricted/ iff it does not
                    // contain any variable which is to be eliminated by
                    // this rule or it contains such variables only at
                    // even powers (which entails that the numbers taken
                    // by the variable parts of the monomial are
                    // non-negative)
                    boolean restrictedMonomial = true;
                    for (final Map.Entry<GPolyVar, BigInteger> varEntry : monomial.getKey().getExponents().entrySet()) {
                        if (!atomUnbounded.contains(varEntry.getKey())
                            || varEntry.getValue().mod(InfRuleSMT.TWO).signum() == 0)
                        {
                            for (int i = varEntry.getValue().intValue() - 1; i >= 0; i--) {
                                vars.add(varEntry.getKey());
                            }
                        } else {
                            restrictedMonomial = false;
                            changed = true;
                            atomChanged = true;
                        }
                    }
                    if (restrictedMonomial) {
                        if (sum == null) {
                            sum = factory.concat(monomial.getValue(), factory.buildVariables(vars));
                        } else {
                            sum = factory.plus(sum, factory.concat(monomial.getValue(), factory.buildVariables(vars)));
                        }
                    } else {
                        GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> remainder;
                        if (vars.isEmpty()) {
                            remainder = factory.buildFromCoeff(monomial.getValue());
                        } else {
                            remainder = factory.concat(monomial.getValue(), factory.buildVariables(vars));
                        }

                        // Here we should need to use EQ only when reasoning
                        // over Z.
                        newConclusions.add(PolyAtom.create(
                            remainder, /*ConstraintType.EQ*/
                            varCoeffConstraintType,
                            interpretation,
                            atom.getTermAtom(),
                            atom.getLeft(),
                            atom.getRight(),
                            atom.getRecommendation()));
                    }
                }
                if (atomChanged) {
                    if (sum != null) {
                        newConclusions.add(PolyAtom.create(
                            sum,
                            atom.getRelation(),
                            interpretation,
                            atom.getTermAtom(),
                            atom.getLeft(),
                            atom.getRight(),
                            atom.getRecommendation()));
                    }
                } else {
                    newConclusions.add(atom);
                }
            } else {
                newConclusions.add(conclusion);
            }
        }
        if (changed) {
            return new Pair<Constraint, InfProofStepInfo>(Implication.create(
                implication.getQuantor(),
                implication.getConditions(),
                ConstraintSet.create(newConclusions),
                implication.getData()), InfProofStepInfo.INF_DUMMY_PROOF);
        } else {
            return new Pair<Constraint, InfProofStepInfo>(implication, InfProofStepInfo.INF_DUMMY_PROOF);
        }
    }

    @Override
    public InfRuleID getID() {
        return InfRuleID.IDP_UNRESTRICTED_VARS;
    }

    @Override
    public String getLongName() {
        return "IDP_UNRESTRICTED_VARS: set coefficients of unrestricted vars to zero";
    }

    @Override
    public String getName() {
        return "IDP_UNRESTRICTED_VARS";
    }

}
