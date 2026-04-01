package aprove.verification.idpframework.Processors.ItpfRules.Execution;

import java.util.*;
import java.util.Map.Entry;

import immutables.*;

/**
 *
 * @author MP
 */
public class ExecutionStepUnderlining {

    public static ExecutionStepUnderlining create(final List<? extends ExecutionMarkable> executionSequence) {
        final Set<ExecutionMarkable> underlined = new HashSet<ExecutionMarkable>();
        final Iterator<? extends ExecutionMarkable> sequenceIterator = executionSequence.iterator();

        ExecutionMarkable source = sequenceIterator.next();
        Map<ExecutionUid, ExecutionMarkable> sourceExecutionMarks = new LinkedHashMap<ExecutionUid, ExecutionMarkable>();
        source.collectExecutionMarks(sourceExecutionMarks);
        while(sequenceIterator.hasNext()) {
            final ExecutionMarkable target = sequenceIterator.next();
            final Map<ExecutionUid, ExecutionMarkable> targetExecutionMarks = new LinkedHashMap<ExecutionUid, ExecutionMarkable>();
            target.collectExecutionMarks(targetExecutionMarks);

            final Map<ExecutionUid, ExecutionMarkable> storedTargetExecMarks = new LinkedHashMap<ExecutionUid, ExecutionMarkable>(targetExecutionMarks);

            ExecutionStepUnderlining.cleanupExecutionMarks(sourceExecutionMarks, targetExecutionMarks);

            underlined.addAll(sourceExecutionMarks.values());

            source = target;
            sourceExecutionMarks = storedTargetExecMarks;
        }

        return new ExecutionStepUnderlining(ImmutableCreator.create(underlined));
    }

    private static Set<ExecutionUid> cleanupExecutionMarks(final Map<ExecutionUid, ExecutionMarkable> sourceExecutionMarks,
        final Map<ExecutionUid, ExecutionMarkable> targetExecutionMarks) {
        final Set<ExecutionUid> unchangedUids = new LinkedHashSet<ExecutionUid>();

        final Iterator<Entry<ExecutionUid, ExecutionMarkable>> sourceIterator =
            sourceExecutionMarks.entrySet().iterator();

        while(sourceIterator.hasNext()) {
            final Entry<ExecutionUid, ExecutionMarkable> sourceEntry = sourceIterator.next();
            final ExecutionMarkable targetValue = targetExecutionMarks.get(sourceEntry.getKey());
            if (targetValue == null) {
                if (!sourceEntry.getKey().isDeletion()) {
                    sourceIterator.remove();
                }
            } else if (sourceEntry.getValue().equals(targetValue)) {
                unchangedUids.add(sourceEntry.getKey());
                targetExecutionMarks.remove(sourceEntry.getKey());
                sourceIterator.remove();
            }
        }

        targetExecutionMarks.keySet().retainAll(sourceExecutionMarks.keySet());

        return unchangedUids;
    }

    private final ImmutableSet<? extends ExecutionMarkable> underlinedObjects;

    public ExecutionStepUnderlining(final ImmutableSet<? extends ExecutionMarkable> underlinedObjects) {
        this.underlinedObjects = underlinedObjects;

    }

    public ImmutableSet<? extends ExecutionMarkable> getUnderlinedObjects() {
        return this.underlinedObjects;
    }

    public boolean isUnderlined(final ExecutionMarkable obj) {
        return this.underlinedObjects.contains(obj);
    }
}
