package aprove.verification.oldframework.Bytecode.Processors;

import static aprove.verification.oldframework.Input.HandlingMode.*;
import static aprove.verification.oldframework.Utility.Collection_Util.*;
import static java.util.stream.Collectors.*;

import java.util.*;
import java.util.Map.*;
import java.util.stream.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.JBCProblem.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.JBCOptions.*;
import aprove.verification.oldframework.Bytecode.OpCodes.*;
import aprove.verification.oldframework.Bytecode.OpCodes.FieldAccess.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.WeightedIntTrs.WeightedIntTrsStraightLineCodeCompressionProcessor.*;

public class SEGraphFlowAnalysisProcessor extends Processor.ProcessorSkeleton {

    public static final Collection<HandlingMode> SupportedGoals = Arrays.asList(RuntimeComplexity, SpaceComplexity);

    public static class Arguments {
        boolean justPropagateFromLoopHeads = true;

        public static StaticOption<Boolean> cliPropagateLowerBounds = new StaticOption<>();
        private InstanceOption<Boolean> propagateLowerBounds = new InstanceOption<Boolean>(false, cliPropagateLowerBounds);

        public boolean propagateLowerBounds() {
            return propagateLowerBounds.get();
        }

        public void setPropagateLowerBounds(boolean b) {
            propagateLowerBounds.set(b);
        }

    }

    private Arguments args;

    @ParamsViaArgumentObject
    public SEGraphFlowAnalysisProcessor(Arguments args) {
        this.args = args;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        JBCTerminationGraphProblem segraph = (JBCTerminationGraphProblem) obl;
        SEGraphFlowAnalysis fa = new SEGraphFlowAnalysis(segraph.getGraph().getStartGraph());
        fa.run();
        if (args.propagateLowerBounds()) {
            return ResultFactory.proved(
                    new JBCTerminationGraphProblem(segraph.getGraph(), fa.getRes()),
                    SoundUpperUnsoundLowerBound.forConcreteBounds(),
                    new InferedRelevantReferencesProof(fa.getRes()));
        } else {
            return ResultFactory.proved(
                    new JBCTerminationGraphProblem(segraph.getGraph(), fa.getRes()),
                    UpperBound.forConcreteBounds(),
                    new InferedRelevantReferencesProof(fa.getRes()));
        }
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof JBCTerminationGraphProblem) {
            TerminationGraph termG = ((JBCTerminationGraphProblem) obl).getGraph();
            return termG.getMethodGraphs().size() == 1 && SupportedGoals.contains(termG.getGoal());
        } else {
            return false;
        }
    }

    private class SEGraphFlowAnalysis {

        MethodGraph segraph;
        HandlingMode goal;
        CollectionMap<Node, AbstractVariableReference> res = new CollectionMap<>();

        SEGraphFlowAnalysis(MethodGraph segraph) {
            this.segraph = segraph;
            this.goal = segraph.getTerminationGraph().getGoal();
        }

        void run() {
            Set<Node> startStates = getStartStates();
            initializeRes(startStates);
            doFixedPointIteration();
        }

        Set<Node> getStartStates() {
            Stream<Node> startInstructions = segraph.getNodes().stream()
                    .filter(x -> x.getState().getCurrentOpCode() instanceof Branch);
            if (args.justPropagateFromLoopHeads) {
                startInstructions = startInstructions.filter(x -> isLoopHead((Branch) x.getState().getCurrentOpCode()));
            }
            Set<Node> nonConstantCosts;
            switch (goal) {
                case RuntimeComplexity: {
                    nonConstantCosts = segraph.getEdges().stream()
                            .filter(e -> e.getLabel() instanceof PredefinedMethodEdge && !((PredefinedMethodEdge) e.getLabel()).getUpperTimeBound().isConstant())
                            .map(e -> e.getStart())
                            .collect(toSet());
                }
                break;
                case SpaceComplexity: {
                    nonConstantCosts = segraph.getEdges().stream()
                            .filter(e ->
                                    (e.getLabel() instanceof PredefinedMethodEdge && !((PredefinedMethodEdge) e.getLabel()).getUpperSpaceBound().isConstant()) ||
                                    (e.getStart().getState().getCurrentOpCode() instanceof ArrayCreate && !e.getStart().getState().getCurrentStackFrame().hasException()))
                            .map(e -> e.getStart())
                            .collect(toSet());
                }
                break;
                default: nonConstantCosts = Collections.emptySet();
            }
            return union(startInstructions.collect(toSet()), nonConstantCosts);
        }

        boolean isLoopHead(Branch b) {
            Set<OpCode> succs = b.getAllPossibleSuccessors();
            if (succs.stream().allMatch(x -> x.mayReach(b) < 0)) {
                return false;
            }
            if (succs.stream().anyMatch(x -> x.mayReach(b) < 0) && succs.stream().anyMatch(x -> x.mayReach(b) >= 0)) {
                return true;
            }
            Set<Set<OpCode>> reachableBackJumps = succs.stream().map(x -> forwardReachableBackJumps(x)).collect(toSet());
            return reachableBackJumps.size() > 1;
        }

        Set<OpCode> forwardReachableBackJumps(OpCode oc) {
            Set<OpCode> res = new LinkedHashSet<>();
            Stack<OpCode> todo = new Stack<>();
            todo.push(oc);
            while (!todo.isEmpty()) {
                OpCode c = todo.pop();
                Set<OpCode> succs = c.getAllPossibleSuccessors();
                if (succs.stream().anyMatch(x -> x.getPos() <= c.getPos())) {
                    res.add(c);
                }
                for (OpCode s: succs) {
                    if (s.getPos() > c.getPos()) {
                        todo.push(s);
                    }
                }
            }
            return res;
        }

        void initializeRes(Set<Node> startStates) {
            for (Node n: startStates) {
                if (n.getState().getCurrentOpCode() instanceof Branch) {
                    Branch branch = (Branch) n.getState().getCurrentOpCode();
                    for (int i = 0; i < branch.getNumberOfArguments(); i++) {
                        res.getNotNullAndAdd(n).add(n.getState().getCurrentStackFrame().getOperandStack().peek(i));
                    }
                } else if (n.getState().getCurrentOpCode() instanceof ArrayCreate) {
                    ArrayCreate ac = (ArrayCreate) n.getState().getCurrentOpCode();
                    for (int i = 0; i < ac.getNumberOfArguments(); i++) {
                        res.getNotNullAndAdd(n).add(n.getState().getCurrentStackFrame().getOperandStack().peek(i));
                    }
                } else {
                    for (Edge e: n.getOutEdges()) {
                        if (e.getLabel() instanceof PredefinedMethodEdge) {
                            Set<String> refNames = new LinkedHashSet<>();
                            switch (goal) {
                                case RuntimeComplexity: refNames.addAll(((PredefinedMethodEdge) e.getLabel()).getUpperTimeBound().getVariables());
                                break;
                                case SpaceComplexity: refNames.addAll(((PredefinedMethodEdge) e.getLabel()).getUpperSpaceBound().getVariables());
                                break;
                            }
                            Set<AbstractVariableReference> refs = n.getState().getReferences().keySet().stream().filter(o -> refNames.contains(o.toString())).collect(toSet());
                            refs.forEach(o -> res.getNotNullAndAdd(n).add(o));
                        }
                    }
                }
            }
        }

        void doFixedPointIteration() {
            boolean changed;
            Map<State, HeapPositions> cache = new LinkedHashMap<>();
            do {
                CollectionMap<Node, AbstractVariableReference> newRes = propagate(cache);
                changed = !res.equals(newRes);
                res = newRes;
            } while (changed);
            return;
        }

        CollectionMap<Node, AbstractVariableReference> propagate(Map<State, HeapPositions> cache) {
            CollectionMap<Node, AbstractVariableReference> newRes = new CollectionMap<>();
            for (Entry<Node, Collection<AbstractVariableReference>> e: res.entrySet()) {
                newRes.put(e.getKey(), new LinkedHashSet<>(e.getValue()));
            }
            for (Entry<Node, Collection<AbstractVariableReference>> resEntry: res.entrySet()) {
                Node node = resEntry.getKey();
                Map<Edge, CollectionMap<AbstractVariableReference, AbstractVariableReference>> preds =
                        resEntry.getKey().getInEdges().stream().collect(toMap(x -> x, x -> x.getRefRenamingEndToStart(cache)));
                propagateFromNode(node, preds, newRes);
            }
            return newRes;
        }

        void propagateFromNode(
                Node node,
                Map<Edge, CollectionMap<AbstractVariableReference, AbstractVariableReference>> preds,
                CollectionMap<Node, AbstractVariableReference> newRes) {
            Collection<AbstractVariableReference> relevantInSuccessor = res.getNotNull(node);
            for (Entry<Edge, CollectionMap<AbstractVariableReference, AbstractVariableReference>> predsEntry: preds.entrySet()) {
                Edge edge = predsEntry.getKey();
                CollectionMap<AbstractVariableReference, AbstractVariableReference> successorToPredecessor = predsEntry.getValue();
                propagateAlongEdge(edge, relevantInSuccessor, successorToPredecessor, newRes);
            }
        }

        void propagateAlongEdge(
                Edge e,
                Collection<AbstractVariableReference> relevantInSuccessor,
                CollectionMap<AbstractVariableReference, AbstractVariableReference> successorToPredecessor,
                CollectionMap<Node, AbstractVariableReference> newRes) {
            Node predecessor = e.getStart();
            Set<AbstractVariableReference> predecessorRefs = predecessor.getState().getReferences().keySet();
            Collection<AbstractVariableReference> relevantInPredecessor = newRes.getNotNullAndAdd(predecessor);
            if (e.getLabel() instanceof EvaluationEdge) {
                propagateAlongEvaluationEdge(
                        e,
                        relevantInSuccessor,
                        successorToPredecessor,
                        relevantInPredecessor,
                        predecessorRefs);
            } else {
                propagateAlongEdgeWithRefRenaming(
                        relevantInSuccessor,
                        successorToPredecessor,
                        relevantInPredecessor,
                        predecessorRefs);
            }
        }

        void propagateAlongEvaluationEdge(
                Edge e,
                Collection<AbstractVariableReference> relevantInSuccessor,
                CollectionMap<AbstractVariableReference, AbstractVariableReference> successorToPredecessor,
                Collection<AbstractVariableReference> relevantInPredecessor,
                Set<AbstractVariableReference> predecessorRefs) {
            State successorState = e.getEnd().getState();
            Node predecessor = e.getStart();
            if (e.getLabel() instanceof PredefinedMethodEdge) {
                PredefinedMethodEdge pme = (PredefinedMethodEdge) e.getLabel();
                Map<AbstractVariableReference, AbstractVariableReference> refRenaming = pme.getRefRenaming().entrySet().stream().collect(toMap(x -> x.getValue(), x -> x.getKey()));
                for (AbstractVariableReference successorRef: relevantInSuccessor) {
                    if (refRenaming.containsKey(successorRef)) {
                        relevantInPredecessor.add(refRenaming.get(successorRef));
                    } else if (predecessorRefs.contains(successorRef)) {
                        relevantInPredecessor.add(successorRef);
                    }
                }
                Set<AbstractVariableReference> refsInPred = e.getStart().getState().getReferences().keySet();
                Map<String, AbstractVariableReference> refsInPredByName = new LinkedHashMap<>();
                for (AbstractVariableReference ref: refsInPred) {
                    if (!ref.pointsToConstant()) {
                        refsInPredByName.put(ref.toString(), ref);
                    }
                }
                Set<String> fromBounds = new LinkedHashSet<>();
                fromBounds.addAll(pme.getLowerSpaceBound().getVariables());
                fromBounds.addAll(pme.getLowerTimeBound().getVariables());
                fromBounds.addAll(pme.getUpperSpaceBound().getVariables());
                fromBounds.addAll(pme.getUpperTimeBound().getVariables());
                relevantInPredecessor.addAll(fromBounds.stream().filter(refsInPredByName::containsKey).map(refsInPredByName::get).collect(toSet()));
            } else {
                propagateAlongEdgeWithoutRefRenaming(relevantInSuccessor, relevantInPredecessor, predecessorRefs);
            }
            propagateBasedOnEdgeInfo(e, relevantInSuccessor, relevantInPredecessor, predecessorRefs);
            OpCode oc = predecessor.getState().getCurrentOpCode();
            if (oc instanceof Inc) {
                handleInc((Inc) oc, relevantInSuccessor, successorToPredecessor, relevantInPredecessor, successorState);
            } else {
                handleInstruction(e, relevantInSuccessor, relevantInPredecessor);
            }
            if (goal == SpaceComplexity && oc instanceof ArrayCreate) {
                ArrayCreate ac = (ArrayCreate) oc;
                OperandStack os = e.getStart().getState().getCurrentStackFrame().getOperandStack();
                for (int i = 0; i < ac.getNumberOfArguments(); i++) {
                    relevantInPredecessor.add(os.peek(i));
                }
            }
            if (oc instanceof FieldAccess) {
                FieldAccess fa = (FieldAccess) oc;
                if (fa.getReadWriteType() == FieldAccessRW.WRITE && !fa.isStatic()) {
                    OperandStack opstack = predecessor.getState().getCurrentStackFrame().getOperandStack();
                    AbstractVariableReference child = opstack.peek(0);
                    AbstractVariableReference parent = opstack.peek(1);
                    for (AbstractVariableReference ref: relevantInSuccessor) {
                        if (ref.pointsToReferenceType()) {
                            Pair<Set<AbstractVariableReference>, Set<AbstractVariableReference>> p =
                                    AnnotationFixups.getRightSquigArrow(ref, true, successorState);
                            Set<AbstractVariableReference> succs = new LinkedHashSet<>();
                            succs.addAll(p.x);
                            succs.addAll(p.y);
                            if (succs.contains(parent)) {
                                relevantInPredecessor.add(child);
                                break;
                            }
                        }
                    }
                }
            }
        }

        void propagateBasedOnEdgeInfo(
                Edge e,
                Collection<AbstractVariableReference> relevantInSuccessor,
                Collection<AbstractVariableReference> relevantInPredecessor,
                Set<AbstractVariableReference> predecessorRefs) {
            for (VariableInformation vi: e.getLabel()) {
                if (vi instanceof SizeRelationInformation) {
                    SizeRelationInformation sri = (SizeRelationInformation) vi;
                    Set<String> vars = sri.getVariables();
                    Set<String> relevantInSuccessorsAsString = relevantInSuccessor.stream().map(x -> x.toString()).collect(toSet());
                    boolean conditionImportant = !areDisjoint(vars, relevantInSuccessorsAsString);
                    if (conditionImportant) {
                        for (AbstractVariableReference ref: predecessorRefs) {
                            if (vars.contains(ref.toString())) {
                                relevantInPredecessor.add(ref);
                            }
                        }
                    }
                } else if (vi instanceof SizeRelationInformation) {
                    SizeRelationInformation sri = (SizeRelationInformation) vi;
                    Set<String> vars = sri.getVariables();
                    Set<String> relevantVars = relevantInSuccessor.stream().map(x -> x.toString()).collect(toSet());
                    if (!areDisjoint(vars, relevantVars)) {
                        Set<AbstractVariableReference> relevantRefs = predecessorRefs.stream().filter(x -> relevantVars.contains(x.toString())).collect(toSet());
                        relevantInPredecessor.addAll(relevantRefs);
                    }
                }
            }
        }

        void propagateAlongEdgeWithoutRefRenaming(
                Collection<AbstractVariableReference> relevantInSuccessor,
                Collection<AbstractVariableReference> relevantInPredecessor,
                Set<AbstractVariableReference> predecessorRefs) {
            for (AbstractVariableReference sucessorRef: relevantInSuccessor) {
                if (predecessorRefs.contains(sucessorRef)) {
                    relevantInPredecessor.add(sucessorRef);
                }
            }
        }

        void propagateAlongEdgeWithRefRenaming(Collection<AbstractVariableReference> relevantInSuccessor,
                CollectionMap<AbstractVariableReference, AbstractVariableReference> successorToPredecessor,
                Collection<AbstractVariableReference> relevantInPredecessor,
                Set<AbstractVariableReference> predecessorRefs) {
            for (AbstractVariableReference successorRef: relevantInSuccessor) {
                if (!successorRef.pointsToConstant()) {
                    if (successorToPredecessor.containsKey(successorRef)) {
                        relevantInPredecessor.addAll(successorToPredecessor.get(successorRef));
                    } else if (predecessorRefs.contains(successorRef)) {
                        relevantInPredecessor.add(successorRef);
                    }
                }
            }
        }

        void handleInc(Inc inc,
                Collection<AbstractVariableReference> relevantInSuccessor,
                CollectionMap<AbstractVariableReference, AbstractVariableReference> successorToPredecessor,
                Collection<AbstractVariableReference> relevantInPredecessor,
                State successorState) {
            int lv = inc.getUsedLocalVariableIndex();
            AbstractVariableReference successorRef = successorState.getCurrentStackFrame().getLocalVariable(lv);
            if (!successorRef.pointsToConstant() && relevantInSuccessor.contains(successorRef)) {
                relevantInPredecessor.addAll(successorToPredecessor.get(successorRef));
            }
        }

        void handleInstruction(
                Edge e,
                Collection<AbstractVariableReference> relevantInSuccessor,
                Collection<AbstractVariableReference> relevantInPredecessor) {
            State successorState = e.getEnd().getState();
            Node predecessor = e.getStart();
            // ignore the case that we just threw an exception
            if (e.getLabel() instanceof MethodStartEdge &&
                    successorState.getCallStack().get(1).hasException() &&
                    !predecessor.getState().getCurrentStackFrame().hasException()) {
                return;
            }
            Pair<Integer, Integer> p = getNumberOfInputsAndOutputs(e);
            int in = p.x;
            int out = p.y;
            for (int i = 0; i < out; i++) {
                AbstractVariableReference outRef = successorState.getCurrentStackFrame().getOperandStack().peek(i);
                if (relevantInSuccessor.contains(outRef)) {
                    for (int j = 0; j < in; j++) {
                        AbstractVariableReference inRef = predecessor.getState().getCurrentStackFrame().getOperandStack().peek(j);
                        relevantInPredecessor.add(inRef);
                    }
                    return;
                }
            }
        }

        Pair<Integer, Integer> getNumberOfInputsAndOutputs(Edge e) {
            if (e.getLabel() instanceof PredefinedMethodEdge) {
                PredefinedMethodEdge pme = (PredefinedMethodEdge) e.getLabel();
                return new Pair<>(pme.getNumArgs(), pme.isVoid() ? 0 : 1);
            } else {
                OpCode oc = e.getStart().getState().getCurrentOpCode();
                return new Pair<>(oc.getNumberOfArguments(), oc.getNumberOfOutputs());
            }
        }

        CollectionMap<Node, AbstractVariableReference> getRes() {
            return res;
        }

    }

    class InferedRelevantReferencesProof extends DefaultProof {

        private CollectionMap<Node, AbstractVariableReference> res;

        public InferedRelevantReferencesProof(CollectionMap<Node, AbstractVariableReference> res) {
            this.res = res;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder s = new StringBuilder();
            s.append("Infered relevant references:");
            s.append(o.newline());
            List<Node> sortedNodes = new ArrayList<>(res.keySet());
            sortedNodes.sort((x, y) -> x.getNodeNumber() - y.getNodeNumber());
            for (Node node: sortedNodes) {
                Collection<AbstractVariableReference> relevantInNode = res.get(node);
                s.append("node").append(o.appSpace()).append(node.getNodeNumber()).append(o.escape(":")).append(o.appSpace());
                for (AbstractVariableReference ref: relevantInNode) {
                    s.append(ref.toString()).append(o.appSpace());
                }
                s.append(o.newline());
            }
            return s.toString();
        }

    }

}
