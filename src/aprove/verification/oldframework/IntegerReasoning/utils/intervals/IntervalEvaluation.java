package aprove.verification.oldframework.IntegerReasoning.utils.intervals;

import java.math.*;
import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;

/**
 * Models a <emph>complete</emph> function of the type IntegerVariable -> IntegerInterval. In order to accurately model
 * a function, this type should be immutable. However, since usual usage consists of updating multiple bounds at once,
 * we chose to keep it mutable.
 * @author Alexander Weinert
 */
public class IntervalEvaluation {

    /**
     * Contains the most exact known intervals for variables. If this map does not contain an interval for a given
     * variable, it is equivalent to it being in the interval (-inf, +inf).
     */
    private final Map<IntegerVariable, IntegerInterval> knownIntervals;

    /**
     * Creates a new function.
     */
    public IntervalEvaluation() {
        this.knownIntervals = new HashMap<>();
    }

    /**
     * Creates a copy of the given IntervalEvaluation.
     * @param other Some other IntervalEvaluation.
     */
    public IntervalEvaluation(final IntervalEvaluation other) {
        this.knownIntervals = new HashMap<>(other.knownIntervals);
    }

    /**
     * @return The set of all variable references and integer intervals that are
     * not (-inf, +inf). Since we model a complete function, all variables
     * that are not a key-value of one entry in this map evaluate to (-inf, +inf)
     */
    public Collection<Map.Entry<IntegerVariable, IntegerInterval>> entrySet() {
        return this.knownIntervals.entrySet();
    }

    public IntegerInterval evaluateExpression(final FunctionalIntegerExpression expression) {
        final IntervalExpressionEvaluator evaluator = new IntervalExpressionEvaluator();
        return evaluator.evaluate(expression, this);
    }

    /**
     * @param variable Some variable
     * @return The interval the value of this variable is in. May be
     * (-inf, +inf), but is never null.
     */
    public IntegerInterval getInterval(final IntegerVariable variable) {
        final IntegerInterval knownInterval = this.knownIntervals.get(variable);
        if (knownInterval != null) {
            return knownInterval;
        } else {
            return IntegerInterval.create(null, null);
        }
    }

    /**
     * Assigns the intersection of the previously known interval and the given
     * interval to the given variable.
     * @param variable Some variable
     * @param interval Some interval
     */
    public void improveInterval(final IntegerVariable variable, final IntegerInterval interval) {
        final IntegerInterval knownInterval = this.getInterval(variable);
        final IntegerInterval intersectedInterval = knownInterval.intersect(interval);
        this.knownIntervals.put(variable, intersectedInterval);
    }

    public IntervalEvaluation intersect(final IntervalEvaluation other) {
        final IntervalEvaluation returnValue = new IntervalEvaluation();

        final Collection<IntegerVariable> thisReferences = new HashSet<>(this.knownIntervals.keySet());
        final Collection<IntegerVariable> otherReferences = new HashSet<>(other.knownIntervals.keySet());

        final Collection<IntegerVariable> bothReferences = new LinkedList<>();
        final Collection<IntegerVariable> onlyThisReferences = new LinkedList<>();
        for (final IntegerVariable thisReference : thisReferences) {
            if (otherReferences.contains(thisReference)) {
                bothReferences.add(thisReference);
                otherReferences.remove(thisReference);
            } else {
                onlyThisReferences.add(thisReference);
            }
        }
        final Collection<IntegerVariable> onlyOtherReferences = new LinkedList<>(otherReferences);

        for (final IntegerVariable varRef : bothReferences) {
            final IntegerInterval thisInterval = this.knownIntervals.get(varRef);
            final IntegerInterval otherInterval = other.knownIntervals.get(varRef);
            returnValue.knownIntervals.put(varRef, thisInterval.intersect(otherInterval));
        }

        for (final IntegerVariable varRef : onlyThisReferences) {
            final IntegerInterval thisInterval = this.knownIntervals.get(varRef);
            returnValue.knownIntervals.put(varRef, thisInterval);
        }

        for (final IntegerVariable varRef : onlyOtherReferences) {
            final IntegerInterval otherInterval = other.knownIntervals.get(varRef);
            returnValue.knownIntervals.put(varRef, otherInterval);
        }

        return returnValue;
    }

    public Collection<IntegerVariable> keySet() {
        return this.knownIntervals.keySet();
    }

    public IntervalEvaluation merge(final IntervalEvaluation other) {
        final IntervalEvaluation returnValue = new IntervalEvaluation(this);
        for (final Map.Entry<IntegerVariable, IntegerInterval> otherEntry : other.knownIntervals.entrySet()) {
            final IntegerVariable variable = otherEntry.getKey();
            final IntegerInterval ourValue = returnValue.getInterval(variable);
            final IntegerInterval theirValue = otherEntry.getValue();
            returnValue.setInterval(variable, ourValue.merge(theirValue));
        }
        return returnValue;
    }

    public IntervalEvaluation rename(final Map<LLVMHeuristicVariable, LLVMHeuristicVariable> renaming) {
        final IntervalEvaluation returnValue = new IntervalEvaluation();
        for (final Map.Entry<LLVMHeuristicVariable, LLVMHeuristicVariable> renamingEntry : renaming.entrySet()) {
            if (!(renamingEntry.getKey() instanceof IntegerVariable && renamingEntry.getValue() instanceof IntegerVariable)) {
                continue;
            }
            final IntegerVariable originalReference = renamingEntry.getKey();
            final IntegerVariable renamedReference = renamingEntry.getValue();

            final IntegerInterval originalInterval = this.getInterval(originalReference);
            final IntegerInterval renamedInterval = returnValue.getInterval(renamedReference);
            returnValue.setInterval(renamedReference, originalInterval.intersect(renamedInterval));
        }
        return returnValue;
    }

    /**
     * Assigns the given interval to the given variable, regardless of already
     * known intervals
     * @param variable Some variable
     * @param interval Some interval
     */
    public void setInterval(final IntegerVariable variable, final IntegerInterval interval) {
        if (interval.isUniversalInterval()) {
            this.knownIntervals.remove(variable);
        } else {
            this.knownIntervals.put(variable, interval);
        }
    }

    public IntegerRelationSet toRelationSet() {
        final IntegerRelationSet returnValue = new IntegerRelationSet();
        for (final Map.Entry<IntegerVariable, IntegerInterval> intervalEntry : this.knownIntervals.entrySet()) {
            final BigInteger lowerBound = intervalEntry.getValue().getLowerBoundIfFinite();
            if (lowerBound != null) {
                returnValue.add(
                    new PlainIntegerRelation(
                        IntegerRelationType.LE,
                        new PlainIntegerConstant(lowerBound),
                        intervalEntry.getKey()
                    )
                );
            }
            final BigInteger upperBound = intervalEntry.getValue().getUpperBoundIfFinite();
            if (upperBound != null) {
                returnValue.add(
                    new PlainIntegerRelation(
                        IntegerRelationType.LE,
                        intervalEntry.getKey(),
                        new PlainIntegerConstant(upperBound)
                    )
                );
            }
        }
        return returnValue;
    }

    @Override
    public String toString() {
        final StringBuilder stringBuilder = new StringBuilder("[");
        final Iterator<Map.Entry<IntegerVariable, IntegerInterval>> iterator = this.knownIntervals.entrySet().iterator();
        while (iterator.hasNext()) {
            final Map.Entry<IntegerVariable, IntegerInterval> entry = iterator.next();
            stringBuilder.append(entry.getKey().toString());
            stringBuilder.append("->");
            stringBuilder.append(entry.getValue().toString());
            if (iterator.hasNext()) {
                stringBuilder.append(";");
            }
        }
        stringBuilder.append("]");
        return stringBuilder.toString();
    }

}
