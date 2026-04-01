package aprove.verification.dpframework.BasicStructures.Matchbounds;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Implementation of a heuristic proposed by Hans Zentema to insert
 * new edges in a certificate graph for MatchBounds.
 *
 * @author <a href="mailto:chang@ariadne.informatik.rwth-aachen.de">Christian Hang</a>
 * @version $Id$
 */
public class ZantemaPathFinder<X> implements PathFinder<X> {

    protected static Logger logger = Logger.getLogger("aprove.verification.oldframework.Rewriting.MatchBounds.ZantemaPathFinder");

    @Override
    public Set<EdgeEquality<AnnotatedFunctionSymbol,X>> insertPath(final MultiGraph<X, AnnotatedFunctionSymbol> graph, final Node<X> startNode, final Node<X> endNode, final List<AnnotatedFunctionSymbol> path) {

        final Set<EdgeEquality<AnnotatedFunctionSymbol, X>> newEdges = new LinkedHashSet<EdgeEquality<AnnotatedFunctionSymbol, X>>();

        List<Node<X>> possibleNodes = new ArrayList<Node<X>>(1);
        possibleNodes.add(endNode);

        // Iterate backwards over the path until the last but one and
        // check for possible nodes we can connect to. Stop if there
        // are no possible nodes remaining

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
                    break;
                }
            }

            if (!foundCompletePath) {
                final EdgeEquality<AnnotatedFunctionSymbol, X> newEdge = new EdgeEquality<AnnotatedFunctionSymbol, X>(startNode, n, symbol);
                if (Globals.DEBUG_COTTO) {
                    ZantemaPathFinder.logger.log(Level.FINER, " -> new edge: " + newEdge + " (no complete path found)\n");
                }
                newEdges.add(newEdge);
            }
        } else {
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
                    ZantemaPathFinder.logger.log(Level.FINER, " -> new edge: " + newEdge + " (complete new path, zantema)\n");
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
