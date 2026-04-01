package aprove.verification.idpframework.Processors.ItpfRules.poly;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.idpframework.Processors.Poly.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class PolyRuleConstraintRefinement<C extends IntRing<C>> extends ContextFreeItpfReplaceRule {

    final PolyRelationsEngine<C> smtEngine;
    private final boolean checkUnsatOnly;

    public PolyRuleConstraintRefinement(final PolyRelationsEngine<C> smtEngine, final boolean checkUnsatOnly) {
        super(new ExportableString("PolyRuleConstraintRefinement"), new ExportableString("PolyRuleConstraintRefinement"));
        this.smtEngine = smtEngine;
        this.checkUnsatOnly = checkUnsatOnly;
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
    public boolean isApplicable(final IDPProblem idp,
        final Itpf formula,
        final ApplicationMode mode) {
        return this.isApplicable(idp);
    }

    @Override
    public boolean isAtomicMark() {
        return false;
    }

    @Override
    public boolean isClauseMark() {
        return true;
    }

    @Override
    public boolean isContextFree() {
        return true;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return this.equals(mark);
    }

    @Override
    public Collection<? extends Mark<?>> getUsedMarks() {
        return Collections.<Mark<?>> singleton(this);
    }

    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause> preProcessClause(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context, final ItpfAndWrapper precondition,
        final ItpfConjClause clause,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException {
        if (!executionRequirements.isComplete()) {
            final List<QuantifiedDisjunction<ItpfConjClause>> conditions = new ArrayList<QuantifiedDisjunction<ItpfConjClause>>(precondition.getSingleFormulas());
            conditions.add(new QuantifiedDisjunction<ItpfConjClause>(ItpfFactory.EMPTY_QUANTORS, clause));

            @SuppressWarnings("unchecked")
            final PolyInterpretation<C> polyInterpretation = (PolyInterpretation<C>) idp.getIdpGraph().getPolyInterpretation();

            final Disjunction<RelationGraph<C>> relationDisjunction = this.getRelations(polyInterpretation,
                Collections.<IVariable<?>>emptySet(),
                new RelationGraph<C>(polyInterpretation.getRing()),
                conditions,
                aborter);

            final LiteralMap nonPolyLiterals = new LiteralMap();
            for (final Map.Entry<ItpfAtom, Boolean> literal : clause.getLiterals().entrySet()) {
                if (!literal.getKey().isPoly()) {
                    nonPolyLiterals.put(literal.getKey(), literal.getValue());
                }
            }

            final Set<ItpfConjClause> newClauses = new LinkedHashSet<ItpfConjClause>();

            final ItpfFactory itpfFactory = idp.getItpfFactory();

            boolean isUnsat = true;
            for (final RelationGraph<C> relation : relationDisjunction) {
                if (!relation.isUnsat()) {
                    isUnsat = false;
                    final LiteralMap newLiterals = new LiteralMap();
                    this.smtEngine.addRelationsToLiterals(polyInterpretation, relation.getEdges(), newLiterals);
                    newLiterals.putAll(nonPolyLiterals);
                    newClauses.add(itpfFactory.createClause(ImmutableCreator.create(newLiterals), clause.getS()));
                }
            }

            if (isUnsat) {
                return new ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>(
                        new QuantifiedDisjunction<ItpfConjClause>(), ImplicationType.EQUIVALENT,
                        ApplicationMode.SingleStep, true);
            } else if (!this.checkUnsatOnly) {
                final QuantifiedDisjunction<ItpfConjClause> clauseDisjunction =
                    new QuantifiedDisjunction<ItpfConjClause>(ItpfFactory.EMPTY_QUANTORS, ImmutableCreator.create(newClauses));

                if (!clauseDisjunction.isSingleton(clause)) {
                    return new ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>(
                            clauseDisjunction,
                            ImplicationType.EQUIVALENT,
                            ApplicationMode.SingleStep,
                            true);
                }
            }
        }

        return new ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>(
                new QuantifiedDisjunction<ItpfConjClause>(ItpfFactory.EMPTY_QUANTORS, clause), ImplicationType.EQUIVALENT,
                ApplicationMode.NoOp, true);
    }

    protected Disjunction<RelationGraph<C>> getRelations(final PolyInterpretation<C> polyInterpretation,
            final Set<IVariable<?>> usedBoundVars,
            final RelationGraph<C> currentRelations,
            final List<QuantifiedDisjunction<ItpfConjClause>> conditions,
            final Abortion aborter) throws AbortionException {
        final LinkedList<QuantifiedDisjunction<ItpfConjClause>> newRemainingConditions = new LinkedList<QuantifiedDisjunction<ItpfConjClause>>(conditions);
        final QuantifiedDisjunction<ItpfConjClause> condition = newRemainingConditions.removeFirst();

        final Set<IVariable<?>> conditionBoundVars;
        if (condition instanceof Itpf) {
            conditionBoundVars = ((Itpf) condition).getBoundVariables();
        } else {
            conditionBoundVars = ItpfUtil.collectBoundVariables(condition.getQuantification());
        }

        final Set<IVariable<?>> newUsedBoundVars;
        if (!conditionBoundVars.isEmpty()) {
            newUsedBoundVars = new LinkedHashSet<IVariable<?>>(usedBoundVars);
            for (final IVariable<?> var : conditionBoundVars) {
                if (!newUsedBoundVars.add(var)) {
                    // bound variables of preconditions should be disjoint
                    return null;
                }
            }
        } else {
            newUsedBoundVars = usedBoundVars;
        }

        final Set<RelationGraph<C>> result = new LinkedHashSet<RelationGraph<C>>();

        for (final ItpfConjClause clause : condition) {
            final Disjunction<RelationGraph<C>> clauseRelations = this.getPolyRelations(polyInterpretation, clause, aborter);
            for (final RelationGraph<C> clauseRelationGraph : clauseRelations) {
                if (!clauseRelationGraph.isUnsat()) {
                    final RelationGraph<C> combinedRelations = this.smtEngine.extendClonedRelations(polyInterpretation, currentRelations, clauseRelationGraph, aborter);

                    if (!newRemainingConditions.isEmpty()) {
                        final Disjunction<RelationGraph<C>> subRelations = this.getRelations(polyInterpretation, newUsedBoundVars, combinedRelations, newRemainingConditions, aborter);
                        if (subRelations == null) {
                            return null;
                        } else {
                            result.addAll(subRelations.asCollection());
                        }
                    } else {
                        result.add(combinedRelations);
                    }
                }
            }
        }

        return new Disjunction<RelationGraph<C>>(ImmutableCreator.create(result));
    }


    private Disjunction<RelationGraph<C>> getPolyRelations(final PolyInterpretation<C> polyInterpretation, final ItpfConjClause clause, final Abortion aborter) throws AbortionException {
        return this.smtEngine.getPropagatedPolyRelations(polyInterpretation, clause, aborter);
    }

    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {
        return null;
    }

}
