package aprove.verification.oldframework.Bytecode.Graphs.Reachability;

import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;

/**
 * Edges of this class are used in the HeapGraph to connect the single
 * instances/arrays. Furthermore, HeapEdges are used to describe the fields that
 * are needed to form a cycle with respect to a 'possibly cyclic' annotation.
 * @author Marc Brockschmidt
 */
public abstract class HeapEdge {
    /**
     * @return unique identifier of this object connection.
     */
    public abstract String getIdentifier();

    /**
     * @return the corresponding NonRootPosition
     */
    public abstract NonRootPosition getNonRootPosition();
}
