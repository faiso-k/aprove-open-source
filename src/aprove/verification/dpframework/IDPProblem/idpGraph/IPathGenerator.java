/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.idpGraph;

import java.util.*;

import aprove.verification.oldframework.Utility.GenericStructures.*;

public interface IPathGenerator {

    /**
     * @param graph
     * @param node
     * @return Pair.x = position of node in path Pair.y
     */
    public List<Pair<Integer, ? extends List<Node>>> paths(IIDependencyGraph graph, Node node);


}
