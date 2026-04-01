package aprove.input.Programs.prolog.processors.toirswt;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.graph.rules.*;
import aprove.verification.oldframework.Utility.Graph.*;

class GraphAnalyzer {

    public Iterable<ArithmeticConnectionPath> getArithmeticConnectionPaths(PrologEvaluationGraph graph) {
        final Collection<ArithmeticConnectionPath> returnValue = new LinkedHashSet<>();

        final Stack<ArithmeticConnectionPath.Builder> builders = new Stack<>();

        builders.add(ArithmeticConnectionPath.Builder.create(graph, graph.getRoot()));
        for(Node<PrologAbstractState> instanceNodeSuccessor : this.getInstanceNodeSuccessors(graph)) {
            builders.add(ArithmeticConnectionPath.Builder.create(graph, instanceNodeSuccessor));
        }
        for(Node<PrologAbstractState> generalizationNodeSuccessor : this.getGeneralizationNodeSuccessors(graph)) {
            builders.add(ArithmeticConnectionPath.Builder.create(graph, generalizationNodeSuccessor));
        }
        for(Node<PrologAbstractState> splitNodeSuccessor : this.getSplitNodeSuccessors(graph)) {
            builders.add(ArithmeticConnectionPath.Builder.create(graph, splitNodeSuccessor));
        }
        for(Node<PrologAbstractState> parallelNodeSuccessor : this.getParallelNodeSuccessors(graph)) {
            builders.add(ArithmeticConnectionPath.Builder.create(graph, parallelNodeSuccessor));
        }
        for(Node<PrologAbstractState> arithCompNodeSuccessor : this.getArithCompNodeSuccessors(graph)) {
            builders.add(ArithmeticConnectionPath.Builder.create(graph, arithCompNodeSuccessor));
        }
        for(Node<PrologAbstractState> isPredicateNodeSuccessor : this.getIsNodeSuccessors(graph)) {
            builders.add(ArithmeticConnectionPath.Builder.create(graph, isPredicateNodeSuccessor));
        }

        while(!builders.isEmpty()) {
            final ArithmeticConnectionPath.Builder currentBuilder = builders.pop();

            if(currentBuilder.canBeExtended()) {
                builders.addAll(currentBuilder.extend());
            }

            if(currentBuilder.canBeBuilt()) {
                returnValue.add(currentBuilder.build());
            }
        }

        return returnValue;
    }

    public Iterable<Node<PrologAbstractState>> getInstanceNodes(PrologEvaluationGraph graph) {
        return graph.getInstanceNodes();
    }

    /**
     * @param graph Some graph. Must not be null.
     * @return All nodes that are the target of an instance edge.
     */
    private Iterable<Node<PrologAbstractState>> getInstanceNodeSuccessors(PrologEvaluationGraph graph) {
        assert graph != null;

        final Collection<Node<PrologAbstractState>> returnValue = new LinkedList<>();
        for(Node<PrologAbstractState> instanceNode : graph.getInstanceNodes()) {
            for(Edge<AbstractInferenceRule, PrologAbstractState> edge : graph.getOutEdges(instanceNode)) {
                if(edge.getObject().rule() == AbstractInferenceRules.INSTANCE) {
                    returnValue.add(edge.getEndNode());
                }
            }
        }

        return returnValue;
    }

    public Iterable<Node<PrologAbstractState>> getGeneralizationNodes(PrologEvaluationGraph graph) {
        return graph.getGeneralizationNodes();
    }

    private Iterable<Node<PrologAbstractState>> getGeneralizationNodeSuccessors(PrologEvaluationGraph graph) {
        assert graph != null;

        final Collection<Node<PrologAbstractState>> returnValue = new LinkedList<>();
        for(Node<PrologAbstractState> instanceNode : graph.getGeneralizationNodes()) {
            for(Edge<AbstractInferenceRule, PrologAbstractState> edge : graph.getOutEdges(instanceNode)) {
                if(edge.getObject().rule() == AbstractInferenceRules.GENERALIZATION) {
                    returnValue.add(edge.getEndNode());
                }
            }
        }

        return returnValue;
    }

    public Iterable<Node<PrologAbstractState>> getParallelNodes(PrologEvaluationGraph graph) {
        return graph.getParallelNodes();
    }

    private Iterable<Node<PrologAbstractState>> getParallelNodeSuccessors(PrologEvaluationGraph graph) {
        assert graph != null;

        final Collection<Node<PrologAbstractState>> returnValue = new LinkedList<>();
        for(Node<PrologAbstractState> instanceNode : graph.getParallelNodes()) {
            for(Edge<AbstractInferenceRule, PrologAbstractState> edge : graph.getOutEdges(instanceNode)) {
                if(edge.getObject().rule() == AbstractInferenceRules.PARALLEL) {
                    returnValue.add(edge.getEndNode());
                }
            }
        }

        return returnValue;
    }

    public Iterable<Node<PrologAbstractState>> getSplitNodes(PrologEvaluationGraph graph) {
        return graph.getSplitNodes();
    }

    /**
     * Since every application of the split rule produces two nodes, this method
     * will return an even number of nodes, two for every node to which we
     * applied the split rule.
     *
     * @param graph Some graph. Must not be null.
     * @return All nodes that are the target of a split edge.
     */
    private Iterable<Node<PrologAbstractState>> getSplitNodeSuccessors(PrologEvaluationGraph graph) {
        assert graph != null;

        final Collection<Node<PrologAbstractState>> returnValue = new LinkedList<>();
        for(Node<PrologAbstractState> splitNode : graph.getSplitNodes()) {
            returnValue.addAll(graph.getOut(splitNode));
        }

        return returnValue;
    }

    public Iterable<Node<PrologAbstractState>> getArithCompNodes(PrologEvaluationGraph graph) {
        return graph.getArithCompNodes();
    }

    /**
     * May return up to three times the number of arith-comp-nodes in the graph, as
     * every arith-comp-node may produce up to three successors (err, true, false)
     * @param graph Some graph. Must not be null.
     * @return All nodes that are the target of an arith-comp-edge.
     */
    private Iterable<Node<PrologAbstractState>> getArithCompNodeSuccessors(PrologEvaluationGraph graph) {
        assert graph != null;

        final Collection<Node<PrologAbstractState>> returnValue = new LinkedList<>();
        for(Node<PrologAbstractState> arithCompNode : graph.getArithCompNodes()) {
            returnValue.addAll(graph.getOut(arithCompNode));
        }

        return returnValue;
    }

    public Iterable<Node<PrologAbstractState>> getIsNodes(PrologEvaluationGraph graph) {
        return graph.getIsNodes();
    }

    private Iterable<Node<PrologAbstractState>> getIsNodeSuccessors(PrologEvaluationGraph graph) {
        assert graph != null;

        final Collection<Node<PrologAbstractState>> returnValue = new LinkedList<>();
        for(Node<PrologAbstractState> instanceNode : graph.getIsNodes()) {
            for(Edge<AbstractInferenceRule, PrologAbstractState> edge : graph.getOutEdges(instanceNode)) {
                if(edge.getObject().rule() == AbstractInferenceRules.PARALLEL) {
                    returnValue.add(edge.getEndNode());
                }
            }
        }

        return returnValue;
    }
}