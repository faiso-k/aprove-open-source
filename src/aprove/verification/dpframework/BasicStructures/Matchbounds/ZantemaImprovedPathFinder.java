package aprove.verification.dpframework.BasicStructures.Matchbounds;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Implementation of a heuristic proposed by Hans Zentema to insert
 * new edges in a certificate graph for MatchBounds.
 * Adds forward edges as an improvement to Zantema's heuristics.
 *
 * @author <a href="mailto:chang@ariadne.informatik.rwth-aachen.de">Christian Hang</a>
 * @version $Id$
 */
public class ZantemaImprovedPathFinder<X> implements PathFinder<X> {

    protected static Logger logger = Logger.getLogger("aprove.verification.oldframework.Rewriting.MatchBounds.ZantemaImprovedPathFinder");

    @Override
    public Set<EdgeEquality<AnnotatedFunctionSymbol,X>> insertPath(final MultiGraph<X, AnnotatedFunctionSymbol> graph, final Node<X> startNode, final Node<X> endNode, final List<AnnotatedFunctionSymbol> path) {

        final Set<EdgeEquality<AnnotatedFunctionSymbol, X>> newEdges = new LinkedHashSet<EdgeEquality<AnnotatedFunctionSymbol, X>>();

        List<Node<X>> possibleNodes = new ArrayList<Node<X>>(1);
        possibleNodes.add(endNode);
        List<Node<X>> possibleForwNodes = new ArrayList<Node<X>>(1);
        possibleForwNodes.add(startNode);

        // Iterate backwards over the path until the last but one and
        // check for possible nodes we can connect to. Stop if there
        // are no possible nodes remaining

        Boolean tryForward = true; // only look for forward edges when no backward edge (zantema) can be found
        Boolean foundForwardPath = false;

        ListIterator<AnnotatedFunctionSymbol> pathIter = path.listIterator(path.size());
        while (pathIter.hasPrevious() && pathIter.previousIndex() > 0 && possibleNodes.size() > 0) {

            final AnnotatedFunctionSymbol symbol = pathIter.previous();
            final Set<Node<X>> tmpSet = new LinkedHashSet<Node<X>>(possibleNodes);
            possibleNodes = new ArrayList<Node<X>>();

            // Check for each possible node whether there is a path to it for
            // the next element of the path
            for (final Node<X> tmpNode : tmpSet) {
                for (final EdgeEquality<AnnotatedFunctionSymbol, X> e : graph.getInEdges(tmpNode)) {
                    if (e.getObject().contains(symbol)) {
                        possibleNodes.add(e.getStartNode());
                    }
                }
            }
            /*
            for (EdgeEquality<Set<AnnotatedFunctionSymbol>, X> e : edges) {
                if (e.getObject().contains(symbol)) {
                    for (Node<X> tmpNode : tmpSet) {
                        if (e.getEndNode().equals(tmpNode)) {
                            possibleNodes.add(e.getStartNode());
                        }
                    }
                }
            }
            */

        }

        if (pathIter.previousIndex() == 0 && possibleNodes.size() > 0) {
            // we iterated along the (whole - 1) new path and found nodes to connect to

            // check whether we can construct the complete path (so find a last edge that fits)
            // If not, insert a new edge (to connect to the path found in the previous loop)

            final Node<X> n = possibleNodes.get(0);
            final AnnotatedFunctionSymbol symbol = pathIter.previous();

            boolean foundCompletePath = false;
            for (final EdgeEquality<AnnotatedFunctionSymbol, X> e : graph.getInEdges(n)) {
                if (e.getStartNode().equals(startNode) && e.getObject().contains(symbol)) {
                    foundCompletePath = true;
                    tryForward = false;
                    break;
                }
            }

            if (!foundCompletePath) {
                final EdgeEquality<AnnotatedFunctionSymbol, X> newEdge = new EdgeEquality<AnnotatedFunctionSymbol, X>(startNode, n, symbol);
                if (Globals.DEBUG_COTTO) {
                    ZantemaImprovedPathFinder.logger.log(Level.FINER, " -> new edge: " + newEdge + " (no complete path found)\n");
                }
                newEdges.add(newEdge);
                tryForward = false;
            }
        }

        if (tryForward) {
            final ListIterator<AnnotatedFunctionSymbol> pathForw = path.listIterator();
            while (pathForw.hasNext() && pathForw.nextIndex() < path.size() - 1 && possibleForwNodes.size() > 0) {

                final AnnotatedFunctionSymbol symbol = pathForw.next();
                final Set<Node<X>> tmpSet = new LinkedHashSet<Node<X>>(possibleForwNodes);
                possibleForwNodes = new ArrayList<Node<X>>();
                // Check for each possible nodes there is a path to it for
                // the next element of the path

                for (final Node<X> tmpNode : tmpSet) {
                    for (final EdgeEquality<AnnotatedFunctionSymbol, X> edge : graph.getOutEdges(tmpNode)) {
                        if (edge.getObject().contains(symbol)) {
                            possibleForwNodes.add(edge.getEndNode());
                        }
                    }
                }
                /*
                Iterator<EdgeEquality<Set<AnnotatedFunctionSymbol>, X>> edgeIter = edges.iterator();
                while (edgeIter.hasNext()) {
                    EdgeEquality<Set<AnnotatedFunctionSymbol>, X> e = edgeIter.next();
                    Iterator<Node<X>> nodeIter = tmpSet.iterator();
                    while (nodeIter.hasNext()) {
                        Node<X> tmpNode = nodeIter.next();
                        if (e.getStartNode().equals(tmpNode) && e.getObject().contains(symbol)) {
                            possibleForwNodes.add(e.getEndNode());
                        }
                    }
                }
                */

            }

            if (pathForw.nextIndex() == path.size() - 1 && possibleForwNodes.size() > 0) {

                // If we are at the last but element of the path, check if
                // we can construct the complete path, otherwise, insert a
                // new edge

                final Node<X> n = possibleForwNodes.get(0);
                final AnnotatedFunctionSymbol symbol = pathForw.next();

                boolean foundCompletePath = false;

                for (final EdgeEquality<AnnotatedFunctionSymbol, X> edge : graph.getOutEdges(n)) {
                    if (edge.getEndNode().equals(endNode) && edge.getObject().contains(symbol)) {
                        foundCompletePath = true;
                        foundForwardPath = true;
                        break;
                    }
                }

                if (!foundCompletePath) {
                    final EdgeEquality<AnnotatedFunctionSymbol, X> newEdge = new EdgeEquality<AnnotatedFunctionSymbol, X>(n, endNode, symbol);
                    graph.addEdge(newEdge);
                    if (Globals.DEBUG_COTTO) {
                        ZantemaImprovedPathFinder.logger.log(Level.FINER, " -> new edge (forw): " + newEdge + "\n");
                    }
                    newEdges.add(newEdge);
                    foundForwardPath = true;
                }
            }
        }

        if (tryForward && !foundForwardPath) { // both methods failed
            // somewhere along the to-be-inserted path we did not find an existing path (to connect to) in the graph

            // heuristics from zantema's paper: insert a whole new path and do not care about the rest of the graph

            Node<X> lastNode = startNode;
            pathIter = path.listIterator();
            while (pathIter.hasNext()) {

                final AnnotatedFunctionSymbol symbol = pathIter.next();
                Node<X> tmpNode = endNode;
                if (pathIter.hasNext()) {
                    tmpNode = new Node<X>();
                }
                final EdgeEquality<AnnotatedFunctionSymbol, X> newEdge = new EdgeEquality<AnnotatedFunctionSymbol, X>(lastNode, tmpNode, symbol);
                if (Globals.DEBUG_COTTO) {
                    ZantemaImprovedPathFinder.logger.log(Level.FINER, " -> new edge: " + newEdge + " (complete new path, zantema)\n");
                }
                newEdges.add(newEdge);
                lastNode = tmpNode;

            }

        }

        // add all the collected new edges to the graph
        for (final EdgeEquality<AnnotatedFunctionSymbol, X> e : newEdges) {
            graph.addEdge(e);
        }
        return newEdges;

    }

}
