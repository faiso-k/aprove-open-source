package aprove.input.Programs.llvm.problems;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.Graph.*;

import java.util.*;

public class LLVMLassoProblem extends LLVMSCCProblem {

    /**
     * The paths in the original graph that lead to this SCC
     */
    private final List<Edge<LLVMEdgeInformation, LLVMAbstractState>> tail;

    public LLVMLassoProblem(SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> s, List<Edge<LLVMEdgeInformation, LLVMAbstractState>> tail, boolean render) {
        super("LLVM Symbolic Execution Lasso", "New LLVM Symbolic Execution Graph Lasso problem", s, render);
        this.tail = tail;
    }
    
    /**
     * SV-COMP: Write SV-COMP witness to GraphML file
     */
    public String buildGraphMLWitness(Map<String, LLVMHeuristicConstRef> varAssign, Abortion aborter) {
        // TODO: IRS
        // if no variable assignment for the lasso is found, stop generating immediately
        if (varAssign == null || varAssign.isEmpty()) {
            return null;
        }

        return GraphMLWitnessBuilder.buildGraphMLWitness(((LLVMSEGraphProblem) this.getParent()).getGraph(), this.getNodes(), this.getSCC().getNodes(), null, varAssign, aborter);
    }

    public boolean contains(Node<LLVMAbstractState> node) {
        for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : this.tail) {
            if (edge.getStartNode().equals(node) || edge.getEndNode().equals(node)) {
                return true;
            }
        }
        if (this.scc.contains(node)) {
            return true;
        }
        return false;
    }
    
    public Set<Node<LLVMAbstractState>> getNodes() {
        Set<Node<LLVMAbstractState>> nodes = new HashSet<>();
        for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : this.tail) {
            nodes.add(edge.getStartNode());
            nodes.add(edge.getEndNode());
        }
        nodes.addAll(this.getSCC().getNodes());
        return nodes;
    }

    /**
     * @return The paths in the original graph that lead to this SCC
     */
    public List<Edge<LLVMEdgeInformation, LLVMAbstractState>> getTail() {
        return tail;
    }

    @Override
    public String export(Export_Util eu) {
        return "Lasso";
        //SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> exportGraph = new LLVMLassoGraph(getSCC());
        //for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : tail) {
        //    exportGraph.addNode(edge.getStartNode());
        //    exportGraph.addNode(edge.getEndNode());
        //    exportGraph.addEdge(edge);
        //}
        //return exportGraph.export("Lasso of symbolic execution graph based on LLVM Program.", this.renderSCC, eu);
    }

    public String findCPathThroughLasso() {
        StringBuilder cPath = new StringBuilder();
        List<Edge<YNM, CState>> stem = new LinkedList<>();
        HashMap<Integer, Node<CState>> graphNodes = new HashMap<>();
        for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : this.tail) {
            Node<LLVMAbstractState> absStart = edge.getStartNode();
            Node<LLVMAbstractState> absEnd = edge.getEndNode();
            CState start = absStart.getObject().toCState(absStart.getNodeNumber());
            CState end = absEnd.getObject().toCState(absEnd.getNodeNumber());
            YNM control = absStart.getObject().getModule().controlResult(absStart.getObject().getProgramPosition(), absEnd.getObject().getProgramPosition());
            Node<CState> startNode = graphNodes.get(start.getNodeID());
            if (startNode == null) {
                startNode = new Node<CState>(start);
                graphNodes.put(start.getNodeID(), startNode);
            }
            Node<CState> endNode = graphNodes.get(end.getNodeID());
            if (endNode == null) {
                endNode = new Node<CState>(end);
                graphNodes.put(end.getNodeID(), endNode);
            }
            Edge<YNM, CState> newEdge = new Edge<>(startNode, endNode, control);
            stem.add(newEdge);
        }
        SimpleGraph<CState, YNM> loop = new SimpleGraph<CState, YNM>();
        for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : this.getSCC().getEdges()) {
            Node<LLVMAbstractState> absStart = edge.getStartNode();
            Node<LLVMAbstractState> absEnd = edge.getEndNode();
            CState start = absStart.getObject().toCState(absStart.getNodeNumber());
            CState end = absEnd.getObject().toCState(absEnd.getNodeNumber());
            YNM control = absStart.getObject().getModule().controlResult(absStart.getObject().getProgramPosition(), absEnd.getObject().getProgramPosition());
            Node<CState> startNode = graphNodes.get(start.getNodeID());
            if (startNode == null) {
                startNode = new Node<CState>(start);
                graphNodes.put(start.getNodeID(), startNode);
            }
            Node<CState> endNode = graphNodes.get(end.getNodeID());
            if (endNode == null) {
                endNode = new Node<CState>(end);
                graphNodes.put(end.getNodeID(), endNode);
            }
            Edge<YNM, CState> newEdge = new Edge<>(startNode, endNode, control);
            loop.addEdge(newEdge);
        }
        Set<CState> seenNodes = new LinkedHashSet<>();
        // stem
        Node<CState> first = stem.get(0).getStartNode();
        seenNodes.add(first.getObject());
        cPath.append(GraphMLFormatter.createWitnessNode(first.getObject(), false));
        int cLine = first.getObject().getCLine();
        Node<CState> last = first;
        Node<CState> nextLast = first;
        YNM control = YNM.MAYBE;
        for (Edge<YNM, CState> edge : stem) {
            Node<CState> start = edge.getStartNode();
            Node<CState> end = edge.getEndNode();
            if (edge.getObject().equals(YNM.YES)) {
                control = YNM.YES;
            } else if (edge.getObject().equals(YNM.NO)) {
                control = YNM.NO;
            }
            // add scc nodes and edges
            if (cLine != start.getObject().getCLine() && start.getObject().getCLine() != end.getObject().getCLine() && start.getObject().getCLine() >= 0) {
                if (!seenNodes.contains(start.getObject())) {
                    cPath.append(GraphMLFormatter.createWitnessNode(start.getObject(), false));
                    seenNodes.add(start.getObject());
                }
                nextLast = start;
                String witnessEdge = GraphMLFormatter.createWitnessEdge(last.getObject(), start.getObject(), control);
                cPath.append(witnessEdge);
                cLine = start.getObject().getCLine();
                control = YNM.MAYBE;
            }
            last = nextLast;
        }
        // loop: we have to start at the last node that was added ("last")
        Node<CState> endOfStem = stem.get(stem.size() - 1).getEndNode();
        Edge<YNM, CState> firstEdgeOfLoop = new Edge<>(last, endOfStem, control);
        loop.addEdge(firstEdgeOfLoop);
        control = YNM.MAYBE;
        Set<Node<CState>> currentNodes = new HashSet<>();
        currentNodes.add(last);
        Set<Node<CState>> visitedNodes = new HashSet<>();
        while (!currentNodes.isEmpty()) {
            Set<Node<CState>> nextCurrentNodes = new HashSet<>();
            Set<Node<CState>> toRemoveFromCurrent = new HashSet<>();
            for (Node<CState> start : currentNodes) {
                // find end nodes of all cLine-paths
                if (visitedNodes.contains(start)) {
                    toRemoveFromCurrent.add(start);
                    continue;
                }
                cLine = start.getObject().getCLine();
                Set<Node<CState>> nodesToVisit = new HashSet<>();
                nodesToVisit.add(start);
                Set<Node<CState>> cLineEndNodes = new HashSet<>();
                boolean changed = true;
                while (changed) {
                    Set<Node<CState>> newNodesToVisit = new HashSet<>();
                    changed = false;
                    for (Node<CState> node : nodesToVisit) {
                        int nodeLine = node.getObject().getCLine();
                        if (nodeLine >= 0 && nodeLine != cLine) {
                            cLineEndNodes.add(node);
                        } else {
                            newNodesToVisit.addAll(loop.getOut(node));
                            changed = true;
                        }
                    }
                    nodesToVisit = newNodesToVisit;
                }
                visitedNodes.add(start);
                nextCurrentNodes.addAll(cLineEndNodes);
                // add edge from start to cLineEndNodes
                for (Node<CState> endNode : cLineEndNodes) {
                    if (!seenNodes.contains(endNode.getObject())) {
                        cPath.append(GraphMLFormatter.createWitnessNode(endNode.getObject(), false));
                        seenNodes.add(endNode.getObject());
                    }
                    String witnessEdge = GraphMLFormatter.createWitnessEdge(start.getObject(), endNode.getObject(), control);
                    cPath.append(witnessEdge);
                }
            }
            currentNodes = nextCurrentNodes;
        }
//        for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : this.getSCC().getEdges()) {
//            System.out.print(edge.getStartNode().getNodeNumber() + " --");
//            System.out.print(edge.getStartNode().getObject().getLineOfCProgram());
//            System.out.println("--> " + edge.getEndNode().getNodeNumber());
//        }
        return cPath.toString();
    }

}
