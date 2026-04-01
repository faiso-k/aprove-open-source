package aprove.verification.oldframework.IntegerReasoning.utils.boundinference;

import java.math.*;
import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.utils.intervals.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Relations of the form c <= x or x <= c for some variable x and some integer
 * constant c are called "bounds". We often have the situation in which we get
 * a relation and want to find out whether this relation implies some bounds.
 *
 * In general, given some relation, we want to find all bounds implied by that
 * relation.
 *
 * However, since it is often infeasible to compute the complete set of implied
 * bounds (since, e.g., x <= 5 implies x <= 6), we only try to find the set of
 * relations R' such that all other bounds that are implied by R are implied by
 * R' as well. This set is always finite, since we only know about a finite set
 * of variables.
 *
 * This inference of bounds is carried out by the method improveBounds. See
 * that method for information on how we infer the set described above.
 *
 * @author Alexander Weinert
 */
public class BoundInference {

    /**
     * The relations already added to this
     */
    private final Map<IntegerVariable, Collection<IntegerRelation>> containingRelations;

    public BoundInference() {
        this.containingRelations = new HashMap<>();
    }

    public BoundInference(final BoundInference other) {
        this.containingRelations = new HashMap<>();
        for (
            Map.Entry<IntegerVariable, Collection<IntegerRelation>> otherEntry : other.containingRelations.entrySet()
        ) {
            this.containingRelations.put(otherEntry.getKey(), new HashSet<>(otherEntry.getValue()));
        }
    }

    /**
     * @param variable Some variable
     * @return The set of relations that contain the given variable. May be empty,
     * but is never null
     */
    private Collection<IntegerRelation> getRelationsContainingVariable(final IntegerVariable variable) {
        if (!this.containingRelations.containsKey(variable)) {
            this.containingRelations.put(variable, new HashSet<IntegerRelation>());
        }
        return this.containingRelations.get(variable);
    }

    /**
     * Registers this relation as a relation containing all variables it
     * contains with this.containingRelations
     * @param relation Some relation
     */
    private void registerAsContainingRelation(final IntegerRelation relation) {
        final Collection<? extends IntegerVariable> references = relation.getVariables();
        if (references.size() < 2) {
            return;
        }
        for (final IntegerVariable reference : references) {
            this.getRelationsContainingVariable(reference).add(relation);
        }
    }

    /**
     * @param relation Some relation
     * @param previousBounds The bounds that were known prior to this inference
     * @return A new IntervalEvaluation that is at least as exact as the given previousBounds,
     * but also contains information gathered by analyzing the given relation as well
     * as the relations given to this object earlier.
     */
    public IntervalEvaluation improveBounds(final IntegerRelation relation, final IntervalEvaluation previousBounds) {
        if (relation.getRelationType().equals(LLVMHeuristicRelationType.NE)) {
            return previousBounds;
        }
        IntervalEvaluation currentEvaluation = new IntervalEvaluation(previousBounds);
        // We catch the special case c = x * y here and infer x <= c and y <= c, if c > 0
        if (
            relation.getRelationType().equals(LLVMHeuristicRelationType.EQ)
            && relation.getLhs() instanceof LLVMHeuristicConstRef
            && ((LLVMHeuristicConstRef) relation.getLhs()).getIntegerValue().compareTo(BigInteger.ZERO) > 0
            && relation.getRhs() instanceof LLVMOperation
            && ((LLVMOperation) relation.getRhs()).getOperation().equals(ArithmeticOperationType.MUL)
            && ((LLVMOperation) relation.getRhs()).getLhs() instanceof IntegerVariable
            && ((LLVMOperation) relation.getRhs()).getRhs() instanceof IntegerVariable
        ) {
            final IntegerInterval interval =
                IntegerInterval.create(null, ((LLVMHeuristicConstRef) relation.getLhs()).getIntegerValue());
            final IntegerVariable lhsVariable = (IntegerVariable) ((LLVMOperation) relation.getRhs()).getLhs();
            final IntegerVariable rhsVariable = (IntegerVariable) ((LLVMOperation) relation.getRhs()).getRhs();
            currentEvaluation.improveInterval(lhsVariable, interval);
            currentEvaluation.improveInterval(rhsVariable, interval);
        }
        this.registerAsContainingRelation(relation);
        final Queue<IntegerRelation> relationsToAnalyze = new LinkedList<>();
        final Collection<IntegerRelation> relationsAnalyzed = new HashSet<>();
        relationsToAnalyze.add(relation);
        final LLVMHeuristicRelationFactory relationFactory =
            LLVMHeuristicRelationFactory.LLVM_HEURISTIC_RELATION_FACTORY;
        final LLVMHeuristicTermFactory termFactory = relationFactory.getTermFactory();
        while (!relationsToAnalyze.isEmpty()) {
            final LLVMHeuristicRelation currentRelation = relationFactory.createRelation(relationsToAnalyze.element());
            relationsAnalyzed.add(currentRelation);
            final IntervalEvaluation inferredEvaluation = new IntervalEvaluation();
            for (final IntegerVariable reference : currentRelation.getVariables()) {
                final Pair<LLVMHeuristicTerm, Boolean> solvedResult =
                    currentRelation.solveFor(termFactory.varRef(reference.getName()));
                if (solvedResult == null) {
                    continue;
                }
                final IntegerInterval evaluatedExpression = currentEvaluation.evaluateExpression(solvedResult.x);
                final boolean refIsEqualToInterval = solvedResult.y == null;
                final boolean refIsLessThanEqualToInterval =
                    solvedResult.y != null && solvedResult.y.booleanValue() == false;
                final boolean refIsGreaterThanEqualToInterval =
                    solvedResult.y != null && solvedResult.y.booleanValue() == true;
                final IntegerInterval referenceInterval;
                if (refIsEqualToInterval) {
                    referenceInterval = evaluatedExpression;
                } else if (refIsLessThanEqualToInterval) {
                    referenceInterval = IntegerInterval.create(null, evaluatedExpression.getUpperBoundIfFinite());
                } else if (refIsGreaterThanEqualToInterval) {
                    referenceInterval = IntegerInterval.create(evaluatedExpression.getLowerBoundIfFinite(), null);
                } else {
                    assert false : "We should never get here";
                    return null;
                }
                inferredEvaluation.setInterval(reference, referenceInterval);
            }

            this.updateQueue(relationsToAnalyze, currentEvaluation, inferredEvaluation, relationsAnalyzed);
            // Only remove the foremost relation at this point so updateQueue does not add it again
            relationsToAnalyze.remove();
            currentEvaluation = currentEvaluation.intersect(inferredEvaluation);
        }

        return currentEvaluation;
    }

    /**
     * We infer bounds on variables by analyzing one relation at a time. When we
     * get new bounds from analyzing one relation, each bound may be better or worse
     * than the previously known one. If it is better, then we have to apply
     * inference to all relations containing that variable again.
     *
     * This method updates the given queue so that all relations that contain
     * an updated variable are in the queue.
     *
     * @param relationsToAnalyze A reference to the queue to be updated
     * @param currentEvaluation The evaluation known prior to bound inference on
     * a single relation
     * @param inferredEvaluation The evaluation inferred by analyzing a single
     * relation
     * @param analyzedRelations The set of relations we have already analyzed
     * in this pass
     */
    private void updateQueue(
        final Queue<IntegerRelation> relationsToAnalyze,
        final IntervalEvaluation currentEvaluation,
        final IntervalEvaluation inferredEvaluation,
        final Collection<IntegerRelation> analyzedRelations)
    {
        for (final Map.Entry<IntegerVariable, IntegerInterval> inferredEvaluationEntry : inferredEvaluation.entrySet()) {
            final IntegerInterval knownInterval = currentEvaluation.getInterval(inferredEvaluationEntry.getKey());
            final IntegerInterval inferredInterval = inferredEvaluationEntry.getValue();
            final boolean inferredIntervalIsImprovement = !inferredInterval.contains(knownInterval);

            if (inferredIntervalIsImprovement) {
                final IntegerVariable improvedVariable = inferredEvaluationEntry.getKey();
                for (final IntegerRelation checkAgainRelation : this.getRelationsContainingVariable(improvedVariable)) {
                    if (!relationsToAnalyze.contains(checkAgainRelation)
                        && !analyzedRelations.contains(checkAgainRelation))
                    {
                        relationsToAnalyze.add(checkAgainRelation);
                    }
                }
            }
        }
    }
}
