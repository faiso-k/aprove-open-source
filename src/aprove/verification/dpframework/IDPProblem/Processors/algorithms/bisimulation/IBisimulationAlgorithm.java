package aprove.verification.dpframework.IDPProblem.Processors.algorithms.bisimulation;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 *
 * @author Martin Pluecker
 */
public interface IBisimulationAlgorithm<T, E> {

    /**
     *
     * @param graph must not coontain any final states
     * @param initialPartition
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public Collection<Set<Node<T>>> getBisimulation(SimpleGraph<T, Set<E>> graph, Collection<Set<Node<T>>> initialPartition, Abortion aborter) throws AbortionException ;

}
