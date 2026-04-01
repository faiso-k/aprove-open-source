package aprove.verification.idpframework.Processors.GraphProcessors.LoopUnroll;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import immutables.*;

/**
 *
 * @author MP
 */
public interface LoopUnrollHeuristic {

    Set<INode> getUnrolledNodes(IDPProblem idp,
        ImmutableMap<INode, IEdge> loopNodes,
        Abortion aborter) throws AbortionException;

}
