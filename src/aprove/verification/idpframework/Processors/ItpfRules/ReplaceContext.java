package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;

import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;

/**
 *
 * @author MP
 */
public interface ReplaceContext {

    public ExecutionMarkable getExecutionSource(ExecutionMarkable target);
    public void addExecutionStep(ExecutionMarkable source, ExecutionMarkable target);
    public void setExecutionMarks();


    public class ReplaceContextSkeleton implements ReplaceContext {

        private final LinkedHashMap<ExecutionMarkable, ExecutionMarkable> executionSteps;

        public ReplaceContextSkeleton() {
            this.executionSteps = new LinkedHashMap<ExecutionMarkable, ExecutionMarkable>();
        }

        @Override
        public void addExecutionStep(final ExecutionMarkable source,
            final ExecutionMarkable target) {
            if (target == null) {
                throw new IllegalArgumentException("target may not be null");
            }

            if (this.executionSteps.containsKey(source)) {
                final ExecutionMarkable s = this.executionSteps.remove(source);
                this.executionSteps.put(target, s);
            } else {
                this.executionSteps.put(target, source);
            }
        }

        @Override
        public ExecutionMarkable getExecutionSource(final ExecutionMarkable target) {
            return this.executionSteps.get(target);
        }

        @Override
        public void setExecutionMarks() {
            for (final Map.Entry<ExecutionMarkable, ExecutionMarkable> executionEntry : this.executionSteps.entrySet()) {
                final ExecutionUid uid = ExecutionUid.create(false);
                executionEntry.getKey().addExecutionMark(uid);
                executionEntry.getValue().addExecutionMark(uid);
            }
        }

    }
}
