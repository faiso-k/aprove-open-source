package aprove.verification.idpframework.Processors.ItpfRules.poly;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.idpframework.Processors.Poly.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author MP
 */
public class PolyRuleInstatiation<C extends SemiRing<C>> extends ContextFreeItpfReplaceRule {

    private final IDPSMTEngine<C> smtEngine;

    public PolyRuleInstatiation(final IDPSMTEngine<C> smtEngine) {
        super(new ExportableString("PolyRuleInstatiation"), new ExportableString("PolyRuleInstatiation"));
        this.smtEngine = smtEngine;
    }

    @Override
    public boolean isSound() {
        return true;
    }

    @Override
    public boolean isComplete() {
        return true;
    }

    @Override
    public boolean isApplicable(final IDPProblem idp) {
        return idp.getIdpGraph().getPolyInterpretation() != null;
    }

    @Override
    public boolean isApplicable(final IDPProblem idp, final Itpf formula, final ApplicationMode mode) {
        return this.isApplicable(idp);
    }

    @Override
    public boolean isAtomicMark() {
        return false;
    }

    @Override
    public boolean isClauseMark() {
        return false;
    }

    @Override
    public boolean isContextFree() {
        return false;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return false;
    }

    @Override
    public Collection<? extends Mark<?>> getUsedMarks() {
        return Collections.<Mark<?>>singleton(this);
    }

    @Override
    protected
        ExecutionResult<? extends QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData>
        processImplication(
            final IDPProblem idp,
            final ReplaceContext.ReplaceContextSkeleton context,
            final ItpfAndWrapper precondition,
            final Set<ITerm<?>> s,
            final ItpfImplication implication,
            final Boolean positive,
            final ImplicationType executionRequirements,
            final ApplicationMode mode,
            final Abortion aborter) throws AbortionException
    {

        ApplicationMode remainingApplications = mode;
        ApplicationMode usedApplications = ApplicationMode.NoOp;
        boolean fixpointReached = true;

        final ItpfImplication newImplication;

        final PolySubstitution instantitations =
            this.getPolyInstantiations(
                idp,
                precondition.getFormula().getQuantification(),
                implication.getPrecondition(),
                precondition.getFormula().getVariables(),
                aborter);

        if (!instantitations.isEmpty()) {
            if (!remainingApplications.isNoOp()) {
                final PolyTermSubstitution substitution =
                    PolyToPolyTermSubstitution.create(
                        instantitations,
                        idp.getPredefinedMap(),
                        idp.getPolyInterpretation());

                newImplication = implication.applySubstitution(substitution);

                remainingApplications = remainingApplications.decreaseOneStep();
                usedApplications = usedApplications.increaseOneStep();
            } else {
                newImplication = implication;
            }
            fixpointReached = false;
        } else {
            newImplication = implication;
        }

        final ExecutionResult<? extends QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> postProcessResult =
            super.processImplication(
                idp,
                context,
                precondition,
                s,
                newImplication,
                positive,
                executionRequirements,
                remainingApplications,
                aborter);

        return postProcessResult.increaseUsedApplications(usedApplications, fixpointReached);
    }

    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(
        final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter)
    {
        // TODO Auto-generated method stub
        return null;
    }

    private PolySubstitution getPolyInstantiations(
        final IDPProblem idp,
        final ImmutableList<ItpfQuantor> quantifications,
        final Itpf precondition,
        final ImmutableSet<IVariable<?>> lockedVariables,
        final Abortion aborter) throws AbortionException
    {
        if (precondition.getClauses().size() != 1) {
            return PolySubstitution.EMPTY_SUBSTITUTION;
        }

        PolySubstitution result = PolySubstitution.EMPTY_SUBSTITUTION;

        final ItpfConjClause clause = precondition.getClauses().iterator().next();

        final Map<IVariable<C>, Signum> varSignums =
            this.smtEngine.getVarSignum(clause, (PolyInterpretation<C>) idp.getPolyInterpretation(), aborter);

        for (final Map.Entry<? extends ItpfAtom, Boolean> literal : clause.getLiterals().entrySet()) {
            if (literal.getKey().isPoly() && literal.getValue()) {
                ItpfPolyAtom<C> polyAtom = (ItpfPolyAtom<C>) literal.getKey();

                final PolyTermSubstitution substitution =
                    PolyToPolyTermSubstitution.create(result, idp.getPredefinedMap(), idp.getPolyInterpretation());

                polyAtom = polyAtom.applySubstitution(substitution);

                final PolyFactory polyFactory = polyAtom.getInterpretation().getFactory();

                Polynomial<C> normalizedPoly = polyAtom.getPoly();
                ConstraintType normalizedConstraintType = polyAtom.getConstraintType();
                if (polyAtom.getConstraintType() == ConstraintType.GT) {
                    normalizedPoly = normalizedPoly.subtract(polyFactory.one(polyAtom.getInterpretation().getRing()));
                    normalizedConstraintType = ConstraintType.GE;
                }

                final Triple<PolyVariable<C>, Polynomial<C>, Boolean> instantitation =
                    this.getPolyInstantiation(
                        polyAtom.getInterpretation(),
                        normalizedPoly,
                        quantifications,
                        varSignums,
                        normalizedConstraintType);

                if (instantitation != null) {
                    if (normalizedConstraintType == ConstraintType.EQ) {
                        result = result.polyCompose(PolySubstitution.create(instantitation.x, instantitation.y));
                    } else if ((!instantitation.y.isZero() || !instantitation.z)
                        && !lockedVariables.contains(instantitation.x))
                    {
                        if (normalizedConstraintType == ConstraintType.GE) {
                            Polynomial<C> replacedVar = polyFactory.create(instantitation.x);
                            if (!instantitation.z) {
                                replacedVar = replacedVar.negate();
                            }
                            result =
                                result.polyCompose(PolySubstitution.create(
                                    instantitation.x,
                                    instantitation.y.add(replacedVar)));
                        }
                    }
                }
            }
        }

        return result;
    }

    private Triple<PolyVariable<C>, Polynomial<C>, Boolean> getPolyInstantiation(
        final PolyInterpretation<C> polyInterpretation,
        final Polynomial<C> poly,
        final ImmutableList<ItpfQuantor> quantifications,
        final Map<IVariable<C>, Signum> varSignums,
        final ConstraintType constraintType)
    {
        if (!this.isLinearAllQuantifiedPoly(polyInterpretation, quantifications, poly, constraintType)) {
            return null;
        }

        /**
         * PolyVariable -> true off variable has positive coeff
         */
        final Map<PolyVariable<C>, Boolean> possibleInstantiations = new LinkedHashMap<PolyVariable<C>, Boolean>();
        final Set<PolyVariable<C>> impossibleInstantiations = new LinkedHashSet<PolyVariable<C>>();

        for (final Map.Entry<Monomial<C>, C> monomialCoeff : poly.getMonomials().entrySet()) {
            final Monomial<C> monomial = monomialCoeff.getKey();
            final C coeff = monomialCoeff.getValue();
            boolean instantiationPossible = monomial.isVariable() && (coeff.isOne() || coeff.negate().isOne());

            if (instantiationPossible) {
                final PolyVariable<C> var = monomial.getVariable();
                if (var.isRealVar()) {
                    final IVariable<C> realVar = (IVariable<C>) var;
                    instantiationPossible = instantiationPossible && !realVar.getDomain().hasBounds();
                }

                if (instantiationPossible && !impossibleInstantiations.contains(var)) {
                    final boolean coeffPos = coeff.isOne();
                    possibleInstantiations.put(var, coeffPos);
                }
            }

            if (!instantiationPossible) {
                possibleInstantiations.keySet().removeAll(monomial.getVariables());
                impossibleInstantiations.addAll(monomial.getVariables());
            }
        }

        if (possibleInstantiations.isEmpty()) {
            return null;
        }

        final PolyVariable<C> instantiationVar =
            this.selectInstantitationVar(
                polyInterpretation,
                poly,
                quantifications,
                possibleInstantiations,
                varSignums,
                constraintType);

        if (instantiationVar == null) {
            return null;
        }

        final boolean negateCoeffs = possibleInstantiations.get(instantiationVar);

        final Map<Monomial<C>, C> otherMonomials = new LinkedHashMap<Monomial<C>, C>();

        for (final Map.Entry<Monomial<C>, C> monomialCoeff : poly.getMonomials().entrySet()) {
            final Monomial<C> monomial = monomialCoeff.getKey();
            final C coeff = monomialCoeff.getValue();
            if (!monomial.getExponents().keySet().contains(instantiationVar)) {
                if (negateCoeffs) {
                    otherMonomials.put(monomial, coeff.negate());
                } else {
                    otherMonomials.put(monomial, coeff);
                }
            }
        }

        return new Triple<PolyVariable<C>, Polynomial<C>, Boolean>(instantiationVar, poly.getFactory().create(
            poly.getRing(),
            ImmutableCreator.create(otherMonomials)), negateCoeffs);
    }

    private boolean isLinearAllQuantifiedPoly(
        final PolyInterpretation<C> polyInterpretation,
        final ImmutableList<ItpfQuantor> quantifications,
        final Polynomial<C> poly,
        final ConstraintType constraintType)
    {
        boolean hasNotExistQuantifiedVar = false;
        for (final Map.Entry<Monomial<C>, C> monomialCoeff : poly.getMonomials().entrySet()) {
            if (constraintType == ConstraintType.EQ) {
                hasNotExistQuantifiedVar = false;
            }
            for (final Map.Entry<? extends PolyVariable<C>, BigInt> exponentEntry : monomialCoeff
                .getKey()
                .getExponents()
                .entrySet())
            {
                final PolyVariable<C> var = exponentEntry.getKey();
                if (!var.isRealVar()) {
                    return false;
                }
                if (!ItpfUtil.isExistQuantified(polyInterpretation, quantifications, (IVariable<C>) var, true)) {
                    if (hasNotExistQuantifiedVar) {
                        return false;
                    }
                    hasNotExistQuantifiedVar = true;

                    if (!exponentEntry.getValue().isOne()) {
                        return false;
                    }
                }
            }
        }

        return true;
    }

    /**
     * @param poly
     * @param varSignums
     * @param constraintType
     * @return selected variable or null
     */
    private PolyVariable<C> selectInstantitationVar(
        final PolyInterpretation<C> polyInterpretation,
        final Polynomial<C> poly,
        final ImmutableList<ItpfQuantor> quantifications,
        final Map<PolyVariable<C>, Boolean> possibleInstantiations,
        final Map<IVariable<C>, Signum> varSignums,
        final ConstraintType constraintType)
    {
        final ImmutableSet<IVariable<C>> polyVariables = poly.getVariables();

        final boolean hasQuantifiedVariable = this.hasQuantifiedVariable(polyVariables, quantifications);

        final Integer constantValueSignum = poly.getConstantPart().getConstantValue().signum();

        // select variable
        for (final Map.Entry<PolyVariable<C>, Boolean> possibleInstantiation : possibleInstantiations.entrySet()) {
            final PolyVariable<C> var = possibleInstantiation.getKey();
            if (hasQuantifiedVariable
                && possibleInstantiation.getKey().isRealVar()
                && !ItpfUtil.isQuantified(quantifications, (IVariable<?>) possibleInstantiation.getKey()))
            {
                continue;
            }

            if (constraintType != ConstraintType.EQ
                && ItpfUtil.isExistQuantified(
                    polyInterpretation,
                    quantifications,
                    (IVariable<?>) possibleInstantiation.getKey(),
                    false))
            {
                continue;
            }

            if (constraintType == ConstraintType.GE && varSignums.containsKey(var)) {
                if (possibleInstantiation.getValue() && varSignums.get(var).isPos() && constantValueSignum >= 0) {
                    continue;
                }

                if (!possibleInstantiation.getValue() && varSignums.get(var).isNeg() && constantValueSignum <= 0) {
                    continue;
                }
            }

            if (constraintType == ConstraintType.EQ) {
                return possibleInstantiation.getKey();
            }

            return possibleInstantiation.getKey();
        }

        return null;
    }

    private boolean hasQuantifiedVariable(
        final ImmutableSet<IVariable<C>> variables,
        final ImmutableList<ItpfQuantor> quantifications)
    {
        boolean hasQuantifiedVariable = false;
        for (final IVariable<C> var : variables) {
            if (ItpfUtil.isQuantified(quantifications, var)) {
                hasQuantifiedVariable = true;
                break;
            }
        }
        return hasQuantifiedVariable;
    }

}
