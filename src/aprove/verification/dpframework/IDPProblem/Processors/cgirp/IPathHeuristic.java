package aprove.verification.dpframework.IDPProblem.Processors.cgirp;

import java.util.*;

import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public interface IPathHeuristic<D extends IPathHeuristic.Data> {


    /**
     * @param node the current node
     * @param paths all generated paths
     * @param currentPath the path that should be extended
     * @param firstNode
     * @param predecs
     * @param lastNode
     * @param succs
     * @param data
     * @return
     */
    public PathDirection decidePathDirection (
            IIDependencyGraph graph, Node node, List<Pair<Integer, ? extends List<Node>>> paths,
            Pair<Integer, ? extends List<Node>> currentPath, Node firstNode,
            ImmutableMap<Node, IdpEdge> predecs, Node lastNode,
            ImmutableMap<Node, IdpEdge> succs, D data);

    public D getInitialData(IIDependencyGraph graph, Node node);

    public static class Data {

        public int totalDivModCount = 0;

    }

}
