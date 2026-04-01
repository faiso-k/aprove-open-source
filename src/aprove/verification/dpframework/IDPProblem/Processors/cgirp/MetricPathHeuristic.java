package aprove.verification.dpframework.IDPProblem.Processors.cgirp;

import java.util.*;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public class MetricPathHeuristic implements IPathHeuristic<MetricPathHeuristic.Data> {

    private final int minLeftSteps;
    private final int minRightSteps;
    private final int maxLeftSteps;
    private final int maxRightSteps;
    private final int maxDegree;
    private final int maxTotalStepCount;
    private final int maxPathCount;
    private final int maxDivModCount;
    private final float dirWeight;
    private final boolean noCondPath;
    private final boolean coundCondNodes;


    @ParamsViaArgumentObject
    public MetricPathHeuristic(Arguments arguments) {
        this.minLeftSteps = arguments.minLeftSteps;
        this.minRightSteps = arguments.minRightSteps;
        this.maxLeftSteps = arguments.maxLeftSteps;
        this.maxRightSteps = arguments.maxRightSteps;
        this.maxDegree = arguments.maxDegree;
        this.maxTotalStepCount = arguments.maxTotalStepCount;
        this.maxPathCount = arguments.maxPathCount;
        this.maxDivModCount = arguments.maxDivModCount;
        this.noCondPath = arguments.noCondPath;
        this.coundCondNodes = arguments.coundCondNodes;
        this.dirWeight = ((float)(this.minLeftSteps + this.maxLeftSteps)) / (this.minRightSteps + this.maxRightSteps);
    }

    @Override
    public PathDirection decidePathDirection(
            IIDependencyGraph graph, Node node, List<Pair<Integer, ? extends List<Node>>> paths,
            Pair<Integer, ? extends List<Node>> currentPath, Node firstNode,
            ImmutableMap<Node, IdpEdge> predecs, Node lastNode,
            ImmutableMap<Node, IdpEdge> succs, Data data) {
        if (predecs.size() == 0) {
            data.totalStepCount -= this.getStepCount(currentPath.y, data.nonCondNodes, 0, currentPath.y.size());
            return PathDirection.Pre;
        } else if (succs.size() == 0) {
            data.totalStepCount -= this.getStepCount(currentPath.y, data.nonCondNodes, 0, currentPath.y.size());
            return PathDirection.Post;
        }
        if (this.noCondPath && !data.nonCondNodes.contains(node)) {
            return PathDirection.None;
        }
        int leftSteps = this.getStepCount(currentPath.y, data.nonCondNodes, 0, currentPath.x+1);
        if (leftSteps < this.minLeftSteps) {
            return PathDirection.Pre;
        }
        int rightSteps = this.getStepCount(currentPath.y, data.nonCondNodes, currentPath.x, currentPath.y.size());
        if (rightSteps < this.minRightSteps) {
            return PathDirection.Post;
        }
        PathDirection decision = PathDirection.None;
        int newPathCount = paths.size();
        boolean prePossible = predecs.size() <= this.maxDegree && leftSteps < this.maxLeftSteps;
        boolean postPossible = succs.size() <= this.maxDegree && rightSteps < this.maxRightSteps;
        IDPPredefinedMap predefinedMap = graph.getNodeAnalysis().getPreDefinedMap();
        if (this.maxDivModCount - data.totalDivModCount < 1) {
            if (prePossible) {
                for (Map.Entry<Node, IdpEdge> pre : predecs.entrySet()) {
                    if (this.hasDivMod(pre.getValue().getItpf(), predefinedMap)) {
                        prePossible = false;
                        break;
                    }
                }
            }
            if (postPossible) {
                for (Map.Entry<Node, IdpEdge> succ : succs.entrySet()) {
                    if (this.hasDivMod(succ.getValue().getItpf(), predefinedMap)) {
                        postPossible = false;
                        break;
                    }
                }
            }
        }

        if (prePossible && ((float)predecs.size()) / succs.size() - this.dirWeight > 0) {
            decision =  PathDirection.Pre;
            int predecCount = predecs.size();
            newPathCount += predecCount -1;
            data.totalStepCount += this.getStepCount(currentPath.y, data.nonCondNodes, 0, currentPath.y.size()) * (predecCount-1) + predecCount;
        } else {
            if (postPossible) {
                decision =  PathDirection.Post;
                int succCount = succs.size();
                newPathCount += succCount -1;
                data.totalStepCount += this.getStepCount(currentPath.y, data.nonCondNodes, 0, currentPath.y.size()) * (succCount-1) + succCount;
            } else if (prePossible) {
                decision = PathDirection.Pre;
                int predecCount = predecs.size();
                newPathCount += predecCount -1;
                data.totalStepCount += this.getStepCount(currentPath.y, data.nonCondNodes, 0, currentPath.y.size()) * (predecCount-1) + predecCount;
            }
        }
        if (data.totalStepCount > this.maxTotalStepCount || newPathCount > this.maxPathCount) {
            decision = PathDirection.None;
        }
        return decision;
    }

    @Override
    public Data getInitialData(IIDependencyGraph graph, Node node) {
        Set<Node> nonCondNodes = new LinkedHashSet<Node>();
        for (Node gNode : graph.getNodes()) {
            if (!Utils.isCondRule(gNode.rule, graph.getNodeAnalysis().getPreDefinedMap())) {
                nonCondNodes.add(gNode);
            }
        }
        if (nonCondNodes.isEmpty()) {
            nonCondNodes.addAll(graph.getNodes());
        }
        return new Data(nonCondNodes);
    }

    protected int getStepCount(List<Node> path, Set<Node> nonCondNodes, int from, int to) {
        if (!this.coundCondNodes) {
            int steps = 0;
            for (int i = from; i < to; i++) {
                if (nonCondNodes.contains(path.get(i))) {
                    steps ++;
                }
            }
            if (steps > 0) {
                return steps -1;
            } else {
                return 0;
            }
        } else {
            return to - from-1;
        }
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

    @Override
    public String toString() {
        StringBuilder b = new StringBuilder();
        b.append("MetricPathGenerator:\nMax Left Steps: ");
        b.append(this.maxLeftSteps);
        b.append("\nMax Right Steps: ");
        b.append(this.maxRightSteps);
        return b.toString();
    }

    public class Data extends IPathHeuristic.Data {

        public final Set<Node> nonCondNodes;
        public int totalStepCount = 0;

        public Data(Set<Node> nonCondNodes) {
            super();
            this.nonCondNodes = nonCondNodes;
        }

    }

    public static class Arguments extends AbstractPathGenerator.Arguments{

        public int minLeftSteps = 1;
        public int minRightSteps = 0;
        public int maxLeftSteps = 8;
        public int maxRightSteps = 3;
        public int maxDegree = 3;
        public int maxTotalStepCount = 100;
        public int maxPathCount = 10;
        public int maxDivModCount = 1;
        public boolean noCondPath = true;
        public boolean coundCondNodes = true;

    }

}
