package aprove.verification.idpframework.Processors.ItpfRules.Execution;

import java.util.*;

/**
 *
 * @author MP
 */
public interface ExecutionMarkable {

    public void addExecutionMark(ExecutionUid mark);

    public boolean isExecutionMarked(ExecutionUid mark);

    public Set<ExecutionUid> getExecutionMarks();


    public void collectExecutionMarks(final Map<ExecutionUid, ExecutionMarkable> executionMarks);

}
