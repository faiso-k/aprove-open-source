package aprove.verification.dpframework.BasicStructures.Matchbounds;

import java.util.*;

import aprove.verification.oldframework.Utility.Graph.*;

/**
 * During the creation of a certificate for proving termination by
 * MatchBounds, several paths have to be inserted into the
 * certifcate-graph. Many heuristics to do this efficiently
 * exist. This interface is provided by <code>MatchBound</code> for
 * different implementations of heuristics. Everytime a new paths has
 * to be inserted, <code>insertPath</code> is invoked by
 * <code>MatchBound</code>.
 *
 * @author <a href="mailto:chang@ariadne.informatik.rwth-aachen.de">Christian Hang</a>
 * @version $Id$
 * @see MatchBound
 * @see MatchBound#getCertificate
 */
public interface PathFinder<X> {

    /**
     * Heuristics to insert a path in a certificate-graph, need to
     * implement this method. The heurist should use existing edges if
     * possible.
     *
     * @param graph the certificate-graph, where the new path needs to
     * be inserted. Every edge is labeled with an
     * <code>AnnotatedFunctionSymbol</code>
     * @param startNode the <code>Node</code> where the new path
     * starts
     * @param endNode the <code>Node</code> where the new path ends
     * @param path a list of
     * <code>AnnotatedFunctionSymbols</code>. Every symbol needs to
     * exists as a lable to an edge between the start and end node
     * after the function call, resulting in the new path
     * @return the new (and only the new!) edges, that were added by
     * this method
     */
    public Set<EdgeEquality<AnnotatedFunctionSymbol,X>> insertPath(MultiGraph<X, AnnotatedFunctionSymbol> graph, Node<X> startNode, Node<X> endNode, List<AnnotatedFunctionSymbol> path);

}
