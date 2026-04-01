package aprove.input.Programs.llvm.segraph;

import java.util.*;

import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * A common interface for paths and loops in an SE graph:
 * Both can be viewed either as a collection of nodes or as a collection of edges
 * @author Hermann Walth
 */
public interface LLVMGraphSection extends Collection<Node<LLVMAbstractState>> {
    /**
     * @return the collection of edges connecting the nodes in this graph section
     */
    public Collection<Edge<LLVMEdgeInformation, LLVMAbstractState>> getEdges();
}
