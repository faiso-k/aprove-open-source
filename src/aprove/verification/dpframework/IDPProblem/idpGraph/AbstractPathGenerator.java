/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.idpGraph;

import java.util.*;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.IDPProblem.Processors.cgirp.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public abstract class AbstractPathGenerator<D extends AbstractPathGenerator.Data> implements IPathGenerator {

    @ParamsViaArgumentObject
    public AbstractPathGenerator(Arguments arguments) {

    }

    @Override
    public List<Pair<Integer, ? extends List<Node>>> paths(
            IIDependencyGraph graph, Node node) {
        List<Pair<Integer, ? extends List<Node>>> paths = new ArrayList<Pair<Integer, ? extends List<Node>>>();
        {
            Pair<Integer, ? extends List<Node>> first = new Pair<Integer, List<Node>>(0, new LinkedList<Node>());
            first.y.add(node);
            paths.add(first);
        }
        IDPPredefinedMap predefinedMap = graph.getNodeAnalysis().getPreDefinedMap();
        D data = this.getInitialData(graph, node);
        boolean changed = false;
        do {
            changed = false;
            int size = paths.size();
            for (int i = 0; i < size; i++) {
                Pair<Integer, ? extends List<Node>> currentPath = paths.get(i);
                LinkedList<Node> pathList = (LinkedList<Node>) currentPath.y;
                Node firstNode = pathList.getFirst();
                Node lastNode = pathList.getLast();
                ImmutableMap<Node, IdpEdge> predecs = graph.getPredecessors(firstNode);
                ImmutableMap<Node, IdpEdge> succs = graph.getSuccessors(lastNode);
                PathDirection result = this.decidePathDirection(graph, node, paths, currentPath, firstNode, predecs, lastNode, succs, data);
                if (result != PathDirection.None) {
                    changed = true;
                    ImmutableMap<Node, IdpEdge> steps;
                    if (result == PathDirection.Post) {
                        steps = succs;
                    } else {
                        steps = predecs;
                    }
                    if (steps.size() == 0) {
                        paths.remove(i);
                        i--;
                        size --;
                    } else {
                        boolean anyDivMod = false;
                        Iterator<Map.Entry<Node, IdpEdge>> stepsIter = steps.entrySet().iterator();
                        Map.Entry<Node, IdpEdge> first = stepsIter.next();
                        while (stepsIter.hasNext()) {
                            Map.Entry<Node, IdpEdge> step = stepsIter.next();
                            LinkedList<Node> path = new LinkedList<Node>(pathList);
                            if (result == PathDirection.Post) {
                                path.addLast(step.getKey());
                                paths.add(new Pair<Integer, LinkedList<Node>>(currentPath.x, path));
                            } else {
                                path.addFirst(step.getKey());
                                paths.add(new Pair<Integer, LinkedList<Node>>(currentPath.x+1, path));
                            }
                            if (!anyDivMod) {
                                anyDivMod = this.hasDivMod(step.getValue().getItpf(), predefinedMap);
                            }
                        }
                        if (result == PathDirection.Post) {
                            pathList.addLast(first.getKey());
                        } else {
                            pathList.addFirst(first.getKey());
                            currentPath.x++;
                        }
                        if (!anyDivMod) {
                            anyDivMod = this.hasDivMod(first.getValue().getItpf(), predefinedMap);
                        }
                        if (anyDivMod) {
                            data.totalDivModCount ++;
                        }
                    }
                }
            }
        } while (changed);
        return paths;
    }

    protected boolean hasDivMod(Itpf formula, IDPPredefinedMap predefinedMap) {
        Set<FunctionSymbol> symbols = formula.getFunctionSymbols();
        for (FunctionSymbol fs : symbols) {
            if (predefinedMap.isDivOrMod(fs)) {
                return true;
            }
        }
        return false;
    }

    protected abstract PathDirection decidePathDirection(
            IIDependencyGraph graph, Node node,
            List<Pair<Integer, ? extends List<Node>>> paths, Pair<Integer, ? extends List<Node>> currentPath,
            Node firstNode, ImmutableMap<Node, IdpEdge> predecs,
            Node lastNode, ImmutableMap<Node, IdpEdge> succs, D data);

    protected abstract D getInitialData(IIDependencyGraph graph, Node node);

    public static class Data {

        public int totalDivModCount = 0;

    }

    public static class Arguments {

    }
}
