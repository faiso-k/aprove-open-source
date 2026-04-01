package aprove.input.Programs.llvm.utils;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

import java.io.File;
import java.util.*;
import java.util.Map.Entry;

public final class GraphMLWitnessBuilder {

    public static String buildGraphMLWitness(LLVMSEGraph graph, Set<Node<LLVMAbstractState>> lassoNodes, Map<Node<LLVMAbstractState>,LLVMConstant> witnessAssignment, Map<String, LLVMHeuristicConstRef> varAssign, Abortion aborter) {
        return buildGraphMLWitness(graph, lassoNodes, lassoNodes, witnessAssignment, varAssign, aborter);
    }
    
    public static String buildGraphMLWitness(
            LLVMSEGraph graph,
            Set<Node<LLVMAbstractState>> lassoNodes,
            Set<Node<LLVMAbstractState>> nontermLoop,
            Map<Node<LLVMAbstractState>,LLVMConstant> witnessAssignment,
            Map<String, LLVMHeuristicConstRef> varAssign,
            Abortion aborter
    ) {
        if (graph.getRoot() == null) {
            System.err.println("Witness cannot be built if there exists no root in the graph.");
            return null;
        }

        Node<LLVMAbstractState> currentNode = graph.getRoot();
        List<Triple<Integer, LLVMAbstractState, YNM>> lasso = new LinkedList<>();
        lasso.add(new Triple<>(currentNode.getNodeNumber(), currentNode.getObject(), YNM.NO));
        LLVMAbstractState currentConcrete = null;
        Set<Integer> visitedNodes = new LinkedHashSet<>();
        while (true) {
            visitedNodes.add(currentNode.getNodeNumber());
            LLVMInstruction currentInstruction = currentNode.getObject().getCurrentInstruction();
            Node<LLVMAbstractState> nextNode = null;
            // three cases:
            // a) no successor -> break
            // b) only one successor -> choose this one
            // c) two successors -> refinement (start is icmp):
            //    evaluate it and choose the successor where the correct truth result is assigned
            if (graph.getOut(currentNode).isEmpty()) {
                break;
            } else if (graph.getOut(currentNode).size() == 1) {
                nextNode = graph.getOut(currentNode).iterator().next();
            } else if (currentInstruction instanceof LLVMICmpInstruction) {
                Iterator<Node<LLVMAbstractState>> iterator = graph.getOut(currentNode).iterator();
                Node<LLVMAbstractState> refinedState1 = iterator.next();
                Node<LLVMAbstractState> refinedState2 = iterator.next();
                LLVMAbstractState firstConcrete = null;
                LLVMAbstractState secondConcrete = null;
                LLVMLiteralRelation refRel = currentInstruction.computeRelation();
                boolean holds = currentConcrete.checkRelation(refRel, aborter).x;
                if (lassoNodes.contains(refinedState1)) {
                    try {
                        firstConcrete = concreteStateOf(refinedState1.getObject(), varAssign, aborter);
                    } catch (InconsistentStateException | IllegalStateException ise) {
                        nextNode = refinedState2;
                    }
                } else {
                    nextNode = refinedState2;
                }
                if (lassoNodes.contains(refinedState2)) {
                    try {
                        secondConcrete = concreteStateOf(refinedState2.getObject(), varAssign, aborter);
                    } catch (InconsistentStateException | IllegalStateException ise) {
                        nextNode = refinedState1;
                    }
                } else {
                    nextNode = refinedState1;
                }
                if (nextNode == null) {
                    if (firstConcrete.checkRelation(refRel, aborter).x == holds) {
                        nextNode = refinedState1;
                    } else {
                        assert (secondConcrete.checkRelation(refRel, aborter).x == holds);
                        nextNode = refinedState2;
                    }
                }
            } else {
                boolean found = false;
                Set<Edge<LLVMEdgeInformation, LLVMAbstractState>> outEdges = graph.getOutEdges(currentNode);
                for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : outEdges) {
                    if (edge.getObject() instanceof LLVMCallAbstractionEdge) {
                        // we are at the call abstraction of a recursive function call
                        nextNode = edge.getEndNode();
                        found = true;
                    }
                }
                if (!found) {
                    Iterator<Node<LLVMAbstractState>> iterator = graph.getOut(currentNode).iterator();
                    Node<LLVMAbstractState> state1 = iterator.next();
                    Node<LLVMAbstractState> state2 = iterator.next();
                    LLVMAbstractState firstConcrete = null;
                    LLVMAbstractState secondConcrete = null;
                    if (lassoNodes.contains(state1)) {
                        try {
                            firstConcrete = concreteStateOf(state1.getObject(), varAssign, aborter);
                        } catch (InconsistentStateException | IllegalStateException ise) {
                            nextNode = state2;
                        }
                    } else {
                        nextNode = state2;
                    }
                    if (lassoNodes.contains(state2)) {
                        try {
                            secondConcrete = concreteStateOf(state2.getObject(), varAssign, aborter);
                        } catch (InconsistentStateException | IllegalStateException ise) {
                            nextNode = state1;
                        }
                    } else {
                        nextNode = state1;
                    }
                }
                if (nextNode == null) {
                    return createWitness(null);
                }
            }
            if (nextNode == null || !lassoNodes.contains(nextNode)) {
                // TODO: Find solution for recursion
            }
            if (witnessAssignment != null) {
                LLVMHeuristicConstRef nondet = (LLVMHeuristicConstRef) witnessAssignment.get(currentNode);
                if (nondet != null) {
                    assert (currentInstruction instanceof LLVMAssignmentInstruction);
                    String newVar = ((LLVMAssignmentInstruction) currentInstruction).getIdentifier().getName();
                    varAssign.put(newVar, nondet);
                }
            }
            LLVMAbstractState nextConcrete;
            try {
                nextConcrete = concreteStateOf(nextNode.getObject(), varAssign, aborter);
            } catch (InconsistentStateException | IllegalStateException ise) {
                return createWitness(null);
            }
            YNM control = currentNode.getObject().getModule().controlResult(currentNode.getObject().getProgramPosition(), nextNode.getObject().getProgramPosition());
            lasso.add(new Triple<>(nextNode.getNodeNumber(), nextConcrete, control));

            // if the next node is already visited before, stop generation
            if (visitedNodes.contains(nextNode.getNodeNumber()) && nontermLoop.contains(nextNode)) {
                break;
            }
            currentNode = nextNode;
            currentConcrete = nextConcrete;
        }
        // due to generalizations, there might be non-concrete states, but we hopefully have only one lasso
        // now compute graphml witness from lasso
        return createWitness(lasso);
    }
    
    public static String buildEmptyGraphMLWitness() {
        return createWitness(null);
    }

    /**
     * Compute the concrete state based on an abstract state and the variable assignment for symbolic variables or program variables
     * <p>
     * The resulting concrete state is still represented with LLVMAbstractState but with additional relation for the variable assignment
     *
     * @param abstractState the abstract state which computation is based on
     * @param varMap        the variable assignment for symbolic variables or program variables
     * @param aborter
     * @return the concrete state if the relations are successfully added, null otherwise
     */
    private static LLVMAbstractState concreteStateOf(LLVMAbstractState abstractState, Map<String, LLVMHeuristicConstRef> varMap, Abortion aborter) {
        LLVMAbstractState concreteState = abstractState;
        for (Entry<String, LLVMHeuristicConstRef> entry : varMap.entrySet()) {
            LLVMSymbolicVariable variable = LLVMHeuristicTermFactory.LLVM_HEURISTIC_TERM_FACTORY.varRef(entry.getKey());
            // check if variable is an address:
            List<LLVMAllocation> allocations = abstractState.getIntegerState().getAllocations();
            boolean isAddress = false;
            for (LLVMAllocation alloc : allocations) {
                Set<LLVMSymbolicVariable> vars = new HashSet<>(alloc.x.getVariables());
                vars.addAll(alloc.y.getVariables());
                if (vars.contains(variable)) {
                    isAddress = true;
                    break;
                }
            }
            if (isAddress) continue;
            if (abstractState.getSymbolicVariables().contains(variable)) {
                // variable mapping for symbolic variables, use the variable directly
                concreteState = concreteState.addRelation(concreteState.getRelationFactory().equalTo(variable, entry.getValue()), aborter);  // assignment is mandatory here, since add relation will generate a new abstract state
            } else {
                // variable mapping for program variables, get the corresponding symbolic variables first
                variable = concreteState.getSymbolicVariableForProgramVariable(entry.getKey());
                if (variable != null) {
                    concreteState = concreteState.addRelation(concreteState.getRelationFactory().equalTo(variable, entry.getValue()), aborter);  // assignment is mandatory here, since add relation will generate a new abstract state
                }
            }
        }
        return concreteState;
    }

    /**
     * SV-COMP: Write SV-COMP witness to GraphML file
     */
    private static String createWitness(List<Triple<Integer, LLVMAbstractState, YNM>> lasso) {
        String programFile = Globals.programFile;
        File file = new File(programFile);
        String programHash;
        try {
            programHash = GraphMLFormatter.calcSHA256(file);
        } catch (Exception e) {
            e.printStackTrace();
            return null;
        }
        StringBuilder graphmlWitness = new StringBuilder();
        graphmlWitness.append(GraphMLFormatter.init(programFile, programHash));
        if (lasso != null) {
            graphmlWitness.append(findCPathThroughLasso(lasso));
        }
        graphmlWitness.append(GraphMLFormatter.finish());
        return graphmlWitness.toString();
    }

    private static String findCPathThroughLasso(List<Triple<Integer, LLVMAbstractState, YNM>> lasso) {
        StringBuilder cPath = new StringBuilder();
        List<Edge<YNM, CState>> edges = new LinkedList<>();
        HashMap<Integer, Node<CState>> graphNodes = new HashMap<>();
        Iterator<Triple<Integer, LLVMAbstractState, YNM>> it = lasso.iterator();
        Triple<Integer, LLVMAbstractState, YNM> firstTriple = it.next();
        LLVMAbstractState absStart = firstTriple.y;
        CState concStart = absStart.toCState(firstTriple.x);
        Node<CState> startNode = new Node<>(concStart);
        graphNodes.put(firstTriple.x, startNode);
        while (it.hasNext()) {
            Triple<Integer, LLVMAbstractState, YNM> next = it.next();
            LLVMAbstractState absNext = next.y;
            CState concNext = absNext.toCState(next.x);
            YNM control = next.z;
            Node<CState> nextNode = graphNodes.get(next.x);
            if (nextNode == null) {
                nextNode = new Node<>(concNext);
                graphNodes.put(next.x, nextNode);
            }
            Edge<YNM, CState> newEdge = new Edge<>(startNode, nextNode, control);
            edges.add(newEdge);
            startNode = nextNode;
        }
        Set<CState> seenNodes = new LinkedHashSet<>();
        Edge<YNM, CState> finalEdge = edges.get(edges.size() - 1);
        Node<CState> finalState = finalEdge.getEndNode();
        Node<CState> first = edges.get(0).getStartNode();
        seenNodes.add(first.getObject());
        cPath.append(GraphMLFormatter.createWitnessNode(first.getObject(), false));
        int cLine = first.getObject().getCLine();
        Node<CState> last = first;
        Node<CState> nextLast = first;
        YNM control = YNM.MAYBE;
        for (Edge<YNM, CState> edge : edges) {
            Node<CState> start = edge.getStartNode();
            Node<CState> end = edge.getEndNode();
            if (edge.getObject().equals(YNM.YES)) {
                control = YNM.YES;
            } else if (edge.getObject().equals(YNM.NO)) {
                control = YNM.NO;
            }
            // add scc nodes and edges
            if ((cLine != start.getObject().getCLine()
                    && start.getObject().getCLine() != end.getObject().getCLine()
                    && start.getObject().getCLine() >= 0
            ) || (start.getNodeNumber() == finalState.getNodeNumber())) {
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
        // if not seen, add last node (in case of other structures than lassos)
        if (!seenNodes.contains(finalState.getObject())) {
            cPath.append(GraphMLFormatter.createWitnessNode(finalState.getObject(), false));
            seenNodes.add(finalState.getObject());
        }
        // add last edge
        if (finalEdge.getObject().equals(YNM.YES)) {
            control = YNM.YES;
        } else if (finalEdge.getObject().equals(YNM.NO)) {
            control = YNM.NO;
        }
        String witnessEdge = GraphMLFormatter.createWitnessEdge(last.getObject(), finalState.getObject(), control);
        cPath.append(witnessEdge);
        return cPath.toString();
    }

}
