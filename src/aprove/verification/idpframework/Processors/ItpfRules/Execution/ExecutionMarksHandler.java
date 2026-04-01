package aprove.verification.idpframework.Processors.ItpfRules.Execution;

import java.util.*;

import aprove.verification.oldframework.Utility.*;

/**
 *
 * @author MP
 */
public class ExecutionMarksHandler implements ExecutionMarkable {

    private final Set<ExecutionUid> marks;
    private final Set<ExecutionUid> unmodifiableMarks;
    private final ExecutionMarkable owner;

    public ExecutionMarksHandler(final ExecutionMarkable owner) {
        this.marks = Collection_Util.<ExecutionUid>createConcurrentHashSet();
        this.unmodifiableMarks = Collections.unmodifiableSet(this.marks);
        this.owner = owner;
    }

    @Override
    public void addExecutionMark(final ExecutionUid mark) {
        this.marks.add(mark);

    }

    @Override
    public boolean isExecutionMarked(final ExecutionUid mark) {
        return this.marks.contains(mark);
    }

    @Override
    public Set<ExecutionUid> getExecutionMarks() {
        return this.unmodifiableMarks;
    }

    @Override
    public void collectExecutionMarks(final Map<ExecutionUid, ExecutionMarkable> executionMarks) {
        for (final ExecutionUid mark : this.marks) {
            executionMarks.put(mark, this.owner);
        }
    }

}
