package aprove.input.Programs.llvm.segraph;

import java.util.*;
import java.util.Map.Entry;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.llvm.processors.*;
import aprove.input.Programs.llvm.processors.LLVMNonterminationProcessor.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * A "loop" in the LLVM symbolic execution graph, used in nontermination proofs.
 * This class is based on an SCC and may therefore contain more than one cycle.
 * This can be check using "isSimpleLoop"
 * @author Hermann Walth
 */
public class LLVMSELoop extends Cycle<LLVMAbstractState> implements LLVMGraphSection {

    /**
     * Serialize me!
     */
    private static final long serialVersionUID = -2673854794619816397L;

    /**
     * The graph this loop is from
     */
    private LLVMSEGraph graph;

    public LLVMSELoop(Set<Node<LLVMAbstractState>> nodes, LLVMSEGraph originalGraph) {
        super(nodes);
        this.graph = originalGraph;
    }

    /**
     * Construct an SMT formula that contains all the
     * interesting constraints along a loop
     * @return An SMT formula for those constraints in the loop that involve
     * only interesting references
     */
    public SMTExpression<SBool> toSMTExp() {
        Set<IntegerVariable> interestingRefs = this.findInterestingReferences();
        LLVMSEPath path = this.toPath();
        List<SMTExpression<SBool>> clauses = new LinkedList<SMTExpression<SBool>>();
        IntegerRelationSet constraints = new IntegerRelationSet(path.getConstraints());
        LLVMEdgeInformation lastEdge = this.graph.getEdge(path.getLast(), path.getFirst()).getObject();
        constraints.addAll(lastEdge.getChangesOnEdge());
        final LLVMRelationFactory relationFactory =
            this.graph.getStrategyParameters().SMTsolver.stateFactory.getRelationFactory();
        // TODO adding equations for the substitution is ok for non-termination, but it would be more precise to use
        // the substitution as a substitution - see also LLVMSEPath
        if (lastEdge instanceof LLVMInstantiationInformation) {
            constraints.addAll(
                LLVMRelation.toSetOfEquations(
                    ((LLVMInstantiationInformation)lastEdge).getReferenceCorrespondenceMap(),
                    relationFactory
                )
            );
        }
        for (IntegerRelation constraint : constraints) {
            Set<? extends Variable> occuringRefs = constraint.getVariables();
            if (interestingRefs.containsAll(occuringRefs)) {
                clauses.add(constraint.toSMTExp());
            }
        }
        for (ImmutablePair<LLVMAllocation, LLVMAllocation> allocs : path.getAllocationPairs()) {
            if (
                interestingRefs.contains(allocs.x.x)
                && interestingRefs.contains(allocs.x.y)
                && interestingRefs.contains(allocs.y.x)
                && interestingRefs.contains(allocs.y.y)
            ) {
                clauses.add(
                    LLVMNonterminationProcessor.getDistinctAllocationFormula(allocs.x, allocs.y, relationFactory)
                );
            }
        }
        for (Edge<LLVMEdgeInformation,LLVMAbstractState> edge : this.getEdges()) {
            if (edge.getObject() instanceof LLVMMethodSkipEdge) {
                LLVMMethodSkipEdge skipEdge = (LLVMMethodSkipEdge) edge.getObject();
                LLVMSEPath skippedPath = LLVMSEPath.backtrackPath(this.graph, edge.getStartNode(), skipEdge.getEndNode()).iterator().next();
                LLVMProblem.logger.fine("Analysing method skip path " + skippedPath.toString());
                clauses.add(skippedPath.toSMTExp());
            }
        }
        return Core.and(clauses);
    }

    /**
     * Find those references that determine the loop's termination behavior.
     * @return The set of interesting references for this loop.
     */
    public Set<IntegerVariable> findInterestingReferences() {
        Set<IntegerVariable> interestingRefs = new LinkedHashSet<IntegerVariable>();
        // get a starting set of interesting references
        for (Node<LLVMAbstractState> exitNode : this.getExitNodes(this.graph)) {
            LLVMAbstractState exitState = exitNode.getObject();
            LLVMInstruction instruction = exitState.getCurrentInstruction();
            Set<String> variables = instruction.getInterestingVariables();
            for (String var : variables) {
                LLVMSymbolicVariable reference = exitState.getSymbolicVariableForProgramVariable(var);
                interestingRefs.add(reference);
            }
        }
        // grow the set of interesting references
        Set<IntegerVariable> oldRefs;
        boolean loaded = false;
        do {
            oldRefs = new LinkedHashSet<IntegerVariable>(interestingRefs);
            for (Node<LLVMAbstractState> node : this) {
                LLVMAbstractState currentState = node.getObject();
                // get more interesting references by looking at each node's instruction
                LLVMInstruction currentInstruction = currentState.getCurrentInstruction();
                LLVMSymbolicVariable producedReference = this.getProducedReference(node);
                if (oldRefs.contains(producedReference)) {
                    Set<String> variables = new LinkedHashSet<>();
                    currentInstruction.collectVariables(variables);
                    Set<LLVMSymbolicVariable> moreRefs = new LinkedHashSet<>();
                    for (String variable : variables) {
                        moreRefs.add(currentState.getSymbolicVariableForProgramVariable(variable));
                    }
                    if (currentInstruction instanceof LLVMLoadInstruction) {
                        loaded = true;
                        // Also mark allocation boundaries corresponding to interesting references
                        for (LLVMSymbolicVariable address : moreRefs) {
                            for (LLVMAllocation alloc : currentState.getAllocations()) {
                                if (address.equals(alloc.x) && alloc.y instanceof LLVMSymbolicVariable) {
                                    moreRefs.add((LLVMSymbolicVariable)alloc.y);
                                }
                                if (address.equals(alloc.y) && alloc.x instanceof LLVMSymbolicVariable) {
                                    moreRefs.add((LLVMSymbolicVariable)alloc.x);
                                }
                            }
                        }
                    }
                    interestingRefs.addAll(moreRefs);
                }
                // if any refs are known to be equal to an interesting ref, they are interesting too
                LLVMIntegerState knowledge = currentState.getIntegerState();
                for (IntegerRelation equation : knowledge.toRelationSet().getEquations()) {
                    if (oldRefs.contains(equation.getLhs())) {
                        FunctionalIntegerExpression rhs = equation.getRhs();
                        if (rhs instanceof LLVMSymbolicVariable) {
                            interestingRefs.add((LLVMSymbolicVariable) rhs);
                        }
                    } else if (oldRefs.contains(equation.getRhs())) {
                        FunctionalIntegerExpression lhs = equation.getLhs();
                        if (lhs instanceof LLVMSymbolicVariable) {
                            interestingRefs.add((LLVMSymbolicVariable) lhs);
                        }
                    }
                }
                if (loaded && currentInstruction instanceof LLVMStoreInstruction) {
                    LLVMStoreInstruction store = (LLVMStoreInstruction)currentInstruction;
                    LLVMSimpleTerm value = currentState.getSimpleTermForLiteral(store.getStoredValue());
                    if (value instanceof IntegerVariable) {
                        interestingRefs.add((IntegerVariable)value);
                    }
                    LLVMSimpleTerm address = currentState.getSimpleTermForLiteral(store.getAddressValue());
                    if (address instanceof IntegerVariable) {
                        interestingRefs.add((IntegerVariable)address);
                    }
                }
            }
            // instantiation edges rename references, mark them too
            for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : this.getEdges()) {
                LLVMEdgeInformation label = edge.getObject();
                if (label instanceof LLVMInstantiationInformation) {
                    LLVMInstantiationInformation instantiation = (LLVMInstantiationInformation)label;
                    Map<LLVMSimpleTerm, LLVMSimpleTerm> renaming = instantiation.getReferenceCorrespondenceMap();
                    for (Map.Entry<LLVMSimpleTerm, LLVMSimpleTerm> entry : renaming.entrySet()) {
                        if (
                            interestingRefs.contains(entry.getKey())
                            && entry.getValue() instanceof LLVMSymbolicVariable
                        ) {
                            interestingRefs.add((LLVMSymbolicVariable)entry.getValue());
                        }
                    }
                }
            }
        } while (!oldRefs.equals(interestingRefs));
        return interestingRefs;
    }

    /**
     * @return the set of edges connecting the nodes in this loop
     */
    @Override
    public Set<Edge<LLVMEdgeInformation, LLVMAbstractState>> getEdges() {
        Set<Edge<LLVMEdgeInformation, LLVMAbstractState>> edges = new LinkedHashSet<>();
        for (Node<LLVMAbstractState> node : this) {
            for (Node<LLVMAbstractState> target : this.graph.getOut(node)) {
                if (this.contains(target)) {
                    edges.add(this.graph.getEdge(node, target));
                }
            }
        }
        return edges;
    }

    /**
     * @return The graph this loop is from.
     */
    public LLVMSEGraph getGraph() {
        return this.graph;
    }

    /**
     * @return An optional containing the loop head node, assuming it is uniquely identifiable.
     * Otherwise, an empty Optional
     */
    public Optional<Node<LLVMAbstractState>> getHeadNode() {
        Set<Edge<LLVMEdgeInformation, LLVMAbstractState>> instanceEdges = new LinkedHashSet<>();
        for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : this.getEdges()) {
            LLVMEdgeInformation label = edge.getObject();
            if (label instanceof LLVMInstantiationInformation) {
                instanceEdges.add(edge);
            }
        }
        Set<Node<LLVMAbstractState>> entryNodes = this.getEntryNodes(this.graph);
        // the head node must be unique
        // TODO even with several entry points there might be a unique head node
        if (entryNodes.size() != 1) {
            return Optional.empty();
        }
        Node<LLVMAbstractState> headCandidate = entryNodes.iterator().next();
        // all instance edges must lead back to the head node
        for (Edge<LLVMEdgeInformation, LLVMAbstractState> instance : instanceEdges) {
            if (!headCandidate.equals(instance.getEndNode())) {
                return Optional.empty();
            }
        }
        return Optional.of(headCandidate);
    }

    /**
     * An extension of BasicInstruction.getProducedVariable()
     * @param node The node whose instruction is interesting
     * @return the LLVMReference produced by evaluating the node's instruction
     */
    public LLVMSymbolicVariable getProducedReference(
        Node<LLVMAbstractState> node
    ) {
        LLVMAbstractState state = node.getObject();
        LLVMInstruction instruction = state.getCurrentInstruction();
        String producedVariable = instruction.getProducedVariable();
        for (Node<LLVMAbstractState> descendant : this.graph.getEvalSuccessors(node)) {
            if (this.contains(descendant)) {
                return descendant.getObject().getSymbolicVariableForProgramVariable(producedVariable);
            }
        }
        throw new IllegalStateException("Unreachable code: At least one successor of a node remains in the SCC");
    }

    /**
     * This class is based on SCCs, not actual loops.
     * Most of the time, you needn't distinguish between SCCs and loops,
     * but in some corner cases, an SCC can contain more than one loop.
     * If that is the case, it is useful to detect it.
     * @return true if this SCC contains exactly one loop,
     *         false otherwise
     */
    public boolean isSimpleLoop() {
        Set<Node<LLVMAbstractState>> pathNodes = new LinkedHashSet<>(this.toPath());
        // if this SCC contains more than one loop,
        // the path won't run through every node
        return pathNodes.containsAll(this);
    }

    /**
     * @param interestingRefs The interesting references.
     * @return The set of formulas encoding paths leaving this loop.
     */
    public Set<ExitFormulas> toExitFormulas(Set<IntegerVariable> interestingRefs) {
        Set<ExitFormulas> res = new LinkedHashSet<ExitFormulas>();
        Optional<Node<LLVMAbstractState>> headOptional = this.getHeadNode();
        if (!headOptional.isPresent()) {
            return null;
        }
        Node<LLVMAbstractState> headNode = headOptional.get();
        for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : this.getExitEdges(this.graph)) {
            // currently, there is only one path without traversing the head node again
            LLVMSEPath path = new LLVMSEPath(this.graph.getPath(headNode, edge.getEndNode()), this.graph);
            if (!LLVMNonterminationProcessor.isPermissiblePath(graph, path)) {
                LLVMProblem.logger.fine( "Aborted analysing this path: " + path + "\n");
                return null;
            }
            Set<IntegerRelation> effects = new LinkedHashSet<IntegerRelation>();
            for (IntegerRelation rel : path.getConstraints().getEquations()) {
                if (interestingRefs.containsAll(rel.getVariables())) {
                    effects.add(rel);
                }
            }
            res.add(new ExitFormulas(edge.getObject().getChangesOnEdge(), effects));
        }
        return res;
    }

    /**
     * Construct an SMT formula that contains all the interesting constraints along a loop such that the interesting
     * references remain unchanged after one loop traversal.
     * @param interestingRefs The interesting references.
     * @return An SMT formula for those constraints in the loop that involve only interesting references.
     */
    public Set<SMTExpression<SBool>> toLoopingFormulas(Set<IntegerVariable> interestingRefs) {
        final LLVMRelationFactory factory = ((LLVMSEGraph)this.graph).getStrategyParameters().SMTsolver.stateFactory
                .getRelationFactory();
        Set<SMTExpression<SBool>> res = new LinkedHashSet<SMTExpression<SBool>>();
        for (LLVMSEPath path : this.toPaths(200,50)) {
            if (path.hasUnknownLoad(interestingRefs)) {
                continue;
            }
            List<SMTExpression<SBool>> clauses = new LinkedList<SMTExpression<SBool>>();
            IntegerRelationSet constraints = path.getConstraints();
            LLVMEdgeInformation lastEdge = this.graph.getEdge(path.getLast(), path.getFirst()).getObject();
            constraints.addAll(lastEdge.getChangesOnEdge());
            if (lastEdge instanceof LLVMInstantiationInformation) {
                constraints.addAll(LLVMRelation.toSetOfEquations(
                        ((LLVMInstantiationInformation) lastEdge).getReferenceCorrespondenceMap(), factory));
            }
            for (IntegerRelation constraint : constraints) {
                if (constraint instanceof LLVMHeuristicRelation) {
                    if (interestingRefs.containsAll(((LLVMHeuristicRelation)constraint).getVariables(false))) {
                        clauses.add(constraint.toSMTExp());
                    }
                } else {
                    if (interestingRefs.containsAll(constraint.getVariables())) {
                        clauses.add(constraint.toSMTExp());
                    }
                }
            }
            for (ImmutablePair<LLVMAllocation, LLVMAllocation> allocs : path.getAllocationPairs()) {
                if (
                    interestingRefs.contains(allocs.x.x)
                    && interestingRefs.contains(allocs.x.y)
                    && interestingRefs.contains(allocs.y.x)
                    && interestingRefs.contains(allocs.y.y)
                ) {
                    clauses.add(
                        LLVMNonterminationProcessor.getDistinctAllocationFormula(
                            allocs.x,
                            allocs.y,
                            this.getGraph().getStrategyParameters().SMTsolver.stateFactory.getRelationFactory()
                        )
                    );
                }
            }
            res.add(Core.and(clauses));
        }
        return res;
    }

    /**
     * Classify all the constraints within the formula as conditions, effects, or correspondences.
     * @param interestingRefs The interesting references.
     * @return A list containing a NonLoopingFormula for each path in the loop.
     * Each NonLoopingFormula contains all the constraints along the path, classified in their respective categories.
     */
    public List<NonLoopingFormulas> toNonLoopingFormulas(Set<IntegerVariable> interestingRefs) {
        List<NonLoopingFormulas> result = new ArrayList<NonLoopingFormulas>();
        for (LLVMSEPath path : this.toPaths(200,50)) {
            if (path.hasUnknownLoad(interestingRefs)) {
                return null;
            }
            if (!LLVMNonterminationProcessor.isPermissiblePath(graph, path)) {
                LLVMProblem.logger.fine( "Aborted analysing this path: " + path + "\n");
                return null;
            }
            Set<IntegerRelation> pathConditions = new LinkedHashSet<IntegerRelation>();
            Set<IntegerRelation> pathEffects = new LinkedHashSet<IntegerRelation>();
            Map<IntegerVariable, IntegerVariable> pathCorrespondence =
                new LinkedHashMap<IntegerVariable, IntegerVariable>();
            List<Node<LLVMAbstractState>> fullPathNodes = new ArrayList<Node<LLVMAbstractState>>(path);
            fullPathNodes.add(path.getFirst());
            LLVMSEPath fullPath = new LLVMSEPath(fullPathNodes, this.graph);
            for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : fullPath.getEdges()) {
                LLVMEdgeInformation edgeLabel = edge.getObject();
                if (edgeLabel instanceof LLVMRefinementInformation) {
                    pathConditions.addAll(edgeLabel.getChangesOnEdge());
                } else if (edgeLabel instanceof LLVMInstantiationInformation) {
                    for (
                        Map.Entry<LLVMSimpleTerm, LLVMSimpleTerm> entry :
                            ((LLVMInstantiationInformation)edgeLabel).getReferenceCorrespondenceMap().entrySet()
                    ) {
                        LLVMSimpleTerm key = entry.getKey();
                        LLVMSimpleTerm value = entry.getValue();
                        if (key instanceof IntegerVariable && value instanceof IntegerVariable) {
                            pathCorrespondence.put((IntegerVariable)key, (IntegerVariable)value);
                        }
                    }
                } else {
                    for (LLVMRelation rel : edgeLabel.getChangesOnEdge()) {
                        if (rel.isEquation()) {
                            pathEffects.add(rel);
                        }
                    }
                }
                pathEffects.addAll(edge.getEndNode().getObject().getIntegerState().toRelationSet().getEquations());
            }
            Iterator<IntegerRelation> it = pathEffects.iterator();
            while (it.hasNext()) {
                if (!interestingRefs.containsAll(it.next().getVariables())) {
                    it.remove();
                }
            }
            Iterator<Entry<IntegerVariable, IntegerVariable>> mapIt = pathCorrespondence.entrySet().iterator();
            while (mapIt.hasNext()) {
                Entry<IntegerVariable, IntegerVariable> entry = mapIt.next();
                if (!(interestingRefs.contains(entry.getKey()) || interestingRefs.contains(entry.getValue()))) {
                    mapIt.remove();
                }
            }
            result.add(new NonLoopingFormulas(pathConditions, pathEffects, pathCorrespondence));
        }
        return result;
    }

    /**
     * @return A path that goes through each node of the loop once, starting from any node in the loop.
     * @deprecated because there may be more than one path through a loop, use toPaths() instead
     */
    @Deprecated
    public LLVMSEPath toPath() {
        List<Node<LLVMAbstractState>> nodes = new LinkedList<>();
        Node<LLVMAbstractState> startNode = this.getEntryNodes(this.graph).iterator().next();
        Node<LLVMAbstractState> nextNode = startNode;
        do {
            nodes.add(nextNode);
            for (Node<LLVMAbstractState> outNode : this.graph.getOut(nextNode)) {
                if (this.contains(outNode)) {
                    nextNode = outNode;
                }
            }
        } while (!nextNode.equals(startNode));
        return new LLVMSEPath(nodes, this.graph);
    }
    
    /**
     * @return a set of path that go from some head node in the loop back to that node,
     * traversing each node of the loop at most once.
     * Every node in the loop is visited by at least one path in the set
     * @param maxPathLength Unbounded if -1
     * @param maxNumberOfPaths Unbounded if -1
     */
    public Set<LLVMSEPath> toPaths(int maxPathLength, int maxNumberOfPaths) {
        Set<LLVMSEPath> result = new LinkedHashSet<>();
        Set<Node<LLVMAbstractState>> startNodes = this.getEntryNodes(this.graph);
        Stack<LinkedList<Node<LLVMAbstractState>>> nextPaths = new Stack<>();
        for (Node<LLVMAbstractState> startNode : startNodes) {
            LinkedList<Node<LLVMAbstractState>> startPath = new LinkedList<>();
            startPath.add(startNode);
            nextPaths.push(startPath);
        }
        int pathLength = 0;
        while (!nextPaths.empty()) {
            pathLength++;
            LinkedList<Node<LLVMAbstractState>> currentPath = nextPaths.pop();
            Node <LLVMAbstractState> nextNode = currentPath.getLast();
            for (Node<LLVMAbstractState> outNode : this.graph.getOut(nextNode)) {
                if (outNode.equals(currentPath.getFirst())) {
                    result.add(new LLVMSEPath(currentPath, this.graph));
                } else if (this.contains(outNode)) {
                    LinkedList<Node<LLVMAbstractState>> pathCopy = new LinkedList<>(currentPath);
                    pathCopy.add(outNode);
                    nextPaths.push(pathCopy);
                }
            }
            if ((maxPathLength >= 0 && pathLength >= maxPathLength) ||
                    (maxNumberOfPaths >= 0 && result.size() >= maxNumberOfPaths)) {
                break;
            }
        }
        return result;
    }

}
