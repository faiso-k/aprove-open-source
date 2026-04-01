package aprove.input.Programs.llvm.processors;

import java.security.*;
import java.util.*;
import java.util.logging.*;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.smt.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Solver.Factories.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.*;
import aprove.verification.oldframework.SMT.Solver.Z3.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Given an LLVM SE graph, attempt to prove nontermination.
 * @author Hermann Walth, cryingshadow
 */
public class LLVMNonterminationProcessor extends Processor.ProcessorSkeleton {

    /**
     * Suffix for labelled variables.
     */
    private static final String SUFFIX = "_nonloop_";

    /**
     * @param graph The SE graph.
     * @param loop The loop to compute a witness for. May be null if the witness is to be computed for a state.
     * @param headNode The head node for the loop.
     * @param loopFormula The formula for the loop or state. May be null (this would be equivalent to the formula True).
     * @param factory The factory for Z3 solvers.
     * @param aborter For abortions.
     * @return A witness for the start state if we can satisfy the loop formula and a formula for backtracking the head
     *         node to the start state.
     */
    public static LLVMAssignmentWitness computeWitness(
        LLVMSEGraph graph,
        LLVMSELoop loop,
        Node<LLVMAbstractState> headNode,
        SMTExpression<SBool> loopFormula,
        Z3ExtSolverFactory factory,
        Abortion aborter
    ) {
        for (LLVMSEPath path : LLVMSEPath.backtrackPath(graph, headNode)) {
            LLVMProblem.logger.log(Level.FINE, "Backtracking along the path " + path + ".\n");
            if (!LLVMNonterminationProcessor.isPermissiblePath(graph, path)) {
                LLVMProblem.logger.log(Level.FINE, "Aborted backtracking along this path.\n");
                continue;
            }
            SMTExpression<SBool> pathFormula = path.toSMTExp();
            Z3Solver z3 = factory.getSMTSolver(SMTLIBLogic.QF_NIA, aborter);
            if (loopFormula != null) {
                z3.addAssertion(loopFormula);
            }
            z3.addAssertion(pathFormula);
            if (z3.checkSAT() == YNM.YES) {
                Optional<Model> lm = z3.getModel();
                if (lm.isPresent()) {
                    Model loopModel = lm.get();
                    // generate a start witness
                    Map<Node<LLVMAbstractState>, LLVMConstant> nondetValues =
                            LLVMNonterminationProcessor.findNondetValues(graph, loop, loopModel);
                    Map<Node<LLVMAbstractState>, LLVMConstant> nondetCalls =
                            LLVMNonterminationProcessor.findNondetValues(graph, path, loopModel);
                    nondetValues.putAll(nondetCalls);
                    String graphmlPath = null;
                    if (Globals.generateGraphmlWitness) {
                        graphmlPath = GraphMLWitnessBuilder.buildGraphMLWitness(graph, graph.getNodes(), nondetValues, new HashMap<>(), aborter);
                    }
                    return new LLVMAssignmentWitness(graphmlPath, graph.getRoot(), loopModel, nondetValues);
                }
            }
        }
        return null;
    }

    /**
     * Bitwise instructions, with the exception of shl and ashr,
     * confuse the nontermination prover because they add insufficient knowledge to the graph.
     * For now, we need to detect bitwise instructions and give up when we encounter them.
     * This method helps in detecting troublesome instructions.
     * @param nodes A collection of nodes in which to look for bitwise instructions
     * @return A set of bitwise instructions found in the nodes
     */
    public static Set<LLVMInstruction> findBlocklistedInstructions(Collection<Node<LLVMAbstractState>> nodes) {
        Set<LLVMInstruction> result = new LinkedHashSet<LLVMInstruction>();
        for (Node<LLVMAbstractState> node : nodes) {
            LLVMInstruction instruction = node.getObject().getCurrentInstruction();
            if (instruction instanceof LLVMBinaryInstruction) {
                LLVMBinaryInstruction binaryInstruction = (LLVMBinaryInstruction) instruction;
                LLVMBinaryOpType operator = binaryInstruction.getOperator();
                switch (operator) {
                    case LSHR:
                    case AND:
                    case OR:
                    case XOR:
                        result.add(binaryInstruction);
                        break;
                    default:
                        break;
                }
            } else if (instruction instanceof LLVMConversionInstruction) {
                LLVMConversionInstruction convInstruction = (LLVMConversionInstruction) instruction;
                if (convInstruction.isZEXT()) {
                    result.add(convInstruction);
                };
            }
        }
        return result;
    }

    /**
     * Find sources of nondeterminism, i.e., calls of declared functions and alloca instructions. Function calls are a
     * source of nondeterminism if the function body is not defined.
     * @param nodes A collection of nodes in which to search for function calls.
     * @return A set of nodes whose states contain call instructions to declared functions.
     */
    public static Set<Node<LLVMAbstractState>> findNondeterminismSources(Collection<Node<LLVMAbstractState>> nodes) {
        Set<Node<LLVMAbstractState>> result = new LinkedHashSet<Node<LLVMAbstractState>>();
        for (Node<LLVMAbstractState> node: nodes) {
            LLVMInstruction currentInstruction = node.getObject().getCurrentInstruction();
            if (currentInstruction instanceof LLVMCallInstruction) {
                LLVMCallInstruction call = (LLVMCallInstruction) currentInstruction;
                String functionName = call.getFunctionName().getName();
                LLVMFnDeclaration functionDecl = node.getObject().getModule().getFunctions().get(functionName);
                if (!(functionDecl instanceof LLVMFnDefinition)) {
                    result.add(node);
                }
            } else if (currentInstruction instanceof LLVMAllocaInstruction) {
                result.add(node);
            }
        }
        return result;
    }

    /**
     * Find values for nondeterministic instructions according to an SMT model.
     * Nondeterministic values must be documented in the nontermination witness.
     * @param graph The LLVM SE Graph
     * @param nodes A collection of nodes in which to look for sources of nondeterminism
     * @param model A model specifying values for a nontermination witness
     * @return A mapping of each node causing nondeterminism to its generated value
     */
    public static Map<Node<LLVMAbstractState>, LLVMConstant> findNondetValues(
        LLVMSEGraph graph,
        Collection<Node<LLVMAbstractState>> nodes,
        Model model
    ) {
        Map<Node<LLVMAbstractState>, LLVMConstant> result = new LinkedHashMap<Node<LLVMAbstractState>, LLVMConstant>();
        if (nodes == null) {
            return result;
        }
        final LLVMTermFactory termFactory =
            graph.getStrategyParameters().SMTsolver.stateFactory.getRelationFactory().getTermFactory();
        for (Node<LLVMAbstractState> node : LLVMNonterminationProcessor.findNondeterminismSources(nodes)) {
            String producedVariable = node.getObject().getCurrentInstruction().getProducedVariable();
            for (Node<LLVMAbstractState> descendant : graph.getEvalSuccessors(node)) {
                if (nodes.contains(descendant)) {
                    LLVMSymbolicVariable producedReference =
                        descendant.getObject().getSymbolicVariableForProgramVariable(producedVariable);
                    if (producedReference != null) {
                        // TODO: check if the produced reference is actually used in the given list of nodes
                        SMTExpression<?> nondetValueSMT = model.get((Symbol<?>) producedReference.toSMTExp());
                        if (nondetValueSMT != null) {
                            LLVMConstant nondetValue =
                                termFactory.constant(nondetValueSMT.accept(new ConstantEvalVisitor()));
                            result.put(node, nondetValue);
                        }
                    }
                }
            }
        }
        return result;
    }

    /**
     * @param alloc1 One allocation entry from an LLVM state
     * @param alloc2 Another allocation entry from an LLVM state
     * @param factory Factory to build relations.
     * @return A formula asserting that these entries do not overlap
     */
    public static SMTExpression<SBool> getDistinctAllocationFormula(
        LLVMAllocation alloc1,
        LLVMAllocation alloc2,
        LLVMRelationFactory factory
    ) {
        if (alloc1.equals(alloc2)) {
            return Core.True;
        } else {
            return Core.or(
                factory.lessThan(alloc1.y, alloc2.x).toSMTExp(),
                factory.lessThan(alloc2.y, alloc1.x).toSMTExp()
            );
        }
    }

    /**
     * We cannot prove nontermination for all possible paths. Cases where that is impossible include:
     * - those bitwise instructions whose results cannot be represented in a simple mathematical formula
     * @param subgraph A path or loop in the symbolic execution graph
     * @return true if we can guarantee that LLVMNonterminationProcessor's proof for this subgraph is correct
     */
    public static boolean isPermissiblePath(LLVMSEGraph graph, LLVMGraphSection subgraph) {
        Set<LLVMInstruction> blocklistedInstructions =
            LLVMNonterminationProcessor.findBlocklistedInstructions(subgraph);
        if (!blocklistedInstructions.isEmpty()) {
            LLVMProblem.logger.fine(
                "Cannot analyse bitwise instructions " + blocklistedInstructions + ".\n"
            );
            return false;
        }
        // TODO fix stack overflows (and do not catch exception)
        try {
            for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : subgraph.getEdges()) {
                if (edge.getObject() instanceof LLVMMethodSkipEdge) {
                    LLVMMethodSkipEdge skipEdge = (LLVMMethodSkipEdge) edge.getObject();
                    Set<List<Node<LLVMAbstractState>>> pathFromCallToReturn = graph.getAllPaths(edge.getStartNode(),skipEdge.getEndNode(),doNotUseCallAbstractionOrIntersectionInstantiationFilter);
                            //LLVMSEPath.backtrackPath(graph,edge.getStartNode(), skipEdge.getEndNode());
                    for(List<Node<LLVMAbstractState>> path : pathFromCallToReturn) {
                        LLVMSEPath asSEPath = new LLVMSEPath(path, graph);
                        if(subgraph.equals(asSEPath)) continue;
                        if(!isPermissiblePath(graph,asSEPath)) {
                            return false;
                        }
                    }
                }
            }
        } catch (StackOverflowError e) {
            return false;
        }
        return true;
    }

    /**
     * @param refs The interesting references.
     * @param correspondence The correspondence map from variables at the end of a path to the ones at the beginning.
     * @param currentLabel The label for the current path.
     * @param resultLabel The label for the result.
     * @return A conjunction of equations between the corresponding (un-)labeled variables.
     */
    private SMTExpression<SBool> connect(
        Set<IntegerVariable> refs,
        Map<IntegerVariable, IntegerVariable> correspondence,
        int currentLabel,
        int resultLabel
    ) {
        List<SMTExpression<SBool>> res = new ArrayList<SMTExpression<SBool>>();
        for (IntegerVariable ref : refs) {
            res.add(
                new PlainIntegerRelation(IntegerRelationType.EQ, ref, this.label(ref, currentLabel)).toSMTExp()
            );
        }
        for (Map.Entry<IntegerVariable, IntegerVariable> entry : correspondence.entrySet()) {
            res.add(
                new PlainIntegerRelation(
                    IntegerRelationType.EQ,
                    this.label(entry.getKey(), resultLabel),
                    this.label(entry.getValue(), currentLabel)
                ).toSMTExp()
            );
        }
        return Core.and(res);
    }

    /**
     * @param obl The obligation.
     * @param oblNode The obligation node.
     * @param aborter The aborter.
     * @param rti The runtime information.
     * @return A pair of a proof and an LLVMSEGraphProblem. This method makes this processor applicable to LLVMProblems
     *         directly by applying the LLVMToSEGraphProcessor first.
     */
    private static ImmutablePair<Proof, LLVMSEGraphProblem> getGraphProblem(
        BasicObligation obl,
        BasicObligationNode oblNode,
        Abortion aborter,
        RuntimeInformation rti
    ) {
        if (obl instanceof LLVMSEGraphProblem) {
            return new ImmutablePair<Proof, LLVMSEGraphProblem>(null, (LLVMSEGraphProblem)obl);
        } else if (obl instanceof LLVMProblem) {
            Result graphResult =
                new LLVMToSEGraphProcessor(new LLVMToSEGraphProcessor.Arguments()).process(obl, oblNode, aborter, rti);
            if (graphResult.getStrategy() instanceof Success) {
                ObligationNodeChild oblChild = graphResult.getObligationChild();
                LLVMSEGraphProblem problem =
                    (LLVMSEGraphProblem)((BasicObligationNode)oblChild.getNewObligation()).getBasicObligation();
                Proof proof = oblChild.getProof();
                return new ImmutablePair<Proof, LLVMSEGraphProblem>(proof, problem);
            } else {
                return null;
            }
        } else {
            throw new InvalidParameterException("Invalid obligation for LLVMNonterminationProcessor");
        }
    }

    /**
     * @param ref Some reference.
     * @param i The label index.
     * @return The labeled reference.
     */
    private IntegerVariable label(IntegerVariable ref, int i) {
        if (ref instanceof IntegerConstant) {
            // this might happen for heuristic states
            return ref;
        }
        return
            FrontendSMT.HEURISTICS.stateFactory.getRelationFactory().getTermFactory().varRef(
                ref.getName() + LLVMNonterminationProcessor.SUFFIX + i
            );
    }

    /**
     * @param rels A set of relations encoding a loop condition or effect formula.
     * @param i The index by which the variables in the resulting formula should be labelled.
     * @return The labelled formula.
     */
    private SMTExpression<SBool> label(Set<? extends IntegerRelation> rels, int i) {
        List<SMTExpression<SBool>> res = new ArrayList<SMTExpression<SBool>>();
        for (IntegerRelation rel : rels) {
            Map<IntegerVariable, IntegerVariable> substitution = new LinkedHashMap<IntegerVariable, IntegerVariable>();
            for (IntegerVariable var : rel.getVariables()) {
                substitution.put(var, this.label(var, i));
            }
            res.add(rel.applySubstitution(substitution).toSMTExp());
        }
        return Core.and(res);
    }

    /**
     * LLVMParameters to be used in method calls
     * NOTE: we usually ignore the SMTSolver field in this structure,
     * since only the Z3 solver supports the get-model operation
     * (as of 2015-01-26)
     */
    private LLVMParameters params;

    /**
     * We often use Z3ExtSolver, so we save an instance of the factory.
     * We don't save an instance of the solver itself because it would
     * remember assertions across different uses, leading to erroneous results
     */
    private Z3ExtSolverFactory z3factory = new Z3ExtSolverFactory();

    /**
     * @param arguments The strategy arguments.
     */
    @ParamsViaArgumentObject
    public LLVMNonterminationProcessor(LLVMNonterminationProcessor.Arguments arguments) {
        super();
        this.params =
            new LLVMParameters(
                arguments.analyzeC,
                false,
                false,
                arguments.useBoundedIntegers,
                arguments.useOptimizations,
                arguments.SMTsolver
            );
    }

    /**
     * @param state A state whose references should be mapped
     * @param model An SMT model representing a concrete state
     * @return a mapping of references to constant values according
     *         to the given model.
     *         Applying this mapping to the state yields the instance
     *         represented by the model.
     */
    @Deprecated
    public Map<LLVMSymbolicVariable, LLVMConstant> evaluateModel(LLVMAbstractState state, Model model) {
        Map<LLVMSymbolicVariable, LLVMConstant> refMap = new LinkedHashMap<>();
        final LLVMTermFactory termFactory = state.getRelationFactory().getTermFactory();
        for (LLVMSymbolicVariable reference : state.getSymbolicVariables()) {
            SMTExpression<?> refValueSMT = model.get((Symbol<?>)reference.toSMTExp());
            if (refValueSMT == null) {
                continue;
            }
            LLVMConstant newRef = termFactory.constant(refValueSMT.accept(new ConstantEvalVisitor()));
            refMap.put(reference, newRef);
        }
        return refMap;
    }

    /**
     * Find a concrete state within a loop that starts a nonterminating cycle.
     * @param loop The loop to analyse.
     * @param sampleNode Any node within the loop, used to construct the witness state.
     * @param interestingRefs The interesting references.
     * @return A witness for nontermination based on the sampleNode, or null if none could be found.
     */
    public LLVMAssignmentWitness findLoopingWitness(
        LLVMSELoop loop,
        Node<LLVMAbstractState> sampleNode,
        Set<IntegerVariable> interestingRefs,
        Abortion aborter
    ) {
        LLVMProblem.logger.log(
            Level.FINE,
            "Interesting references of the loop: " + interestingRefs + "\n"
        );
        for (SMTExpression<SBool> loopFormula : loop.toLoopingFormulas(interestingRefs)) {
            LLVMProblem.logger.log(Level.FINE, "Looping SMT formula: " + loopFormula + ".\n");
            LLVMAssignmentWitness witness =
                LLVMNonterminationProcessor.computeWitness(
                    loop.getGraph(),
                    loop,
                    sampleNode,
                    loopFormula,
                    this.z3factory,
                    aborter
                );
            if (witness != null) {
                return witness;
            }
        }
        return null;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof LLVMSEGraphProblem || obl instanceof LLVMProblem;
    }

    @Override
    public Result process(
        BasicObligation obl,
        BasicObligationNode oblNode,
        Abortion aborter,
        RuntimeInformation rti
    ) throws AbortionException {
        this.params =
            new LLVMParameters(
                this.params.analyzeC,
                this.params.proveMemorySafety,
                this.params.proveFreeOfMemoryLeaks,
                this.params.useBoundedIntegers,
                this.params.useOptimizations,
                this.params.SMTsolver
            );
        ImmutablePair<Proof, LLVMSEGraphProblem> parentNode =
            LLVMNonterminationProcessor.getGraphProblem(obl, oblNode, aborter, rti);
        if (parentNode == null) {
            return ResultFactory.unsuccessful("Graph construction was unsuccessful.");
        }
        Proof priorProof = parentNode.x;
        LLVMSEGraphProblem problem = parentNode.y;
        for (LLVMSELoop loop: problem.getGraph().getLoops()) {
            Set<IntegerVariable> interestingRefs = loop.findInterestingReferences();
            for (LLVMSEPath subloopAsPath : loop.toPaths(200,50)) {
                LLVMSELoop subloop =
                    new LLVMSELoop(new LinkedHashSet<>(subloopAsPath), problem.getGraph());
                LLVMAssignmentWitness witness = this.processLoop(subloop, interestingRefs, aborter);
                if (witness != null) {
                    return ResultFactory.disproved(new LLVMNonterminationProof(priorProof, problem, witness));
                }
            }
            LLVMAssignmentWitness witness =
                this.proveNonLoopingNonTermination(
                    loop,
                    loop.toNonLoopingFormulas(interestingRefs),
                    loop.toExitFormulas(interestingRefs),
                    interestingRefs,
                    aborter
                );
            if (witness != null) {
                return ResultFactory.disproved(new LLVMNonterminationProof(priorProof, problem, witness));
            }
        }
        return ResultFactory.unsuccessful("Could not prove nontermination for any of the loops.");
    }

    /**
     * Analyse a single loop for nontermination.
     * @param loop The loop to analyse.
     * @param interestingRefs The interesting references.
     * @return A proof of nontermination for this loop, or null if it couldn't be proven.
     */
    public LLVMAssignmentWitness processLoop(LLVMSELoop loop, Set<IntegerVariable> interestingRefs, Abortion aborter) {
        // refuse to analyse non-simple loops
        LLVMProblem.logger.fine("\nProcessing loop " + loop + ":\n\n");
        if (!loop.isSimpleLoop()) {
            LLVMProblem.logger.fine("Loop is too complicated to analyse!\n");
            return null;
        }
        // check if we can actually process this loop
        if (!LLVMNonterminationProcessor.isPermissiblePath(loop.getGraph(),loop)) {
            LLVMProblem.logger.fine( "Aborted analysing this loop\n");
            return null;
        }
        // choose any node of the loop as the witness
        Node<LLVMAbstractState> witnessNode = loop.iterator().next();
        LLVMAssignmentWitness witness = this.findLoopingWitness(loop, witnessNode, interestingRefs, aborter);
        if (witness == null) {
            LLVMProblem.logger.fine("Could not find a looping witness\n");
            return null;
        }
        return witness;
    }

    /**
     * @param loop The SCC to prove non-termination for.
     * @param nonLoopingFormulas The loop conditions and effects for all paths through the loop.
     * @param exitFormulas The set of formulas encoding paths leaving the loop.
     * @param interestingRefs The interesting references.
     * @return A witness for a non-terminating execution of the loop or null if no such witness can be found.
     */
    private LLVMAssignmentWitness proveNonLoopingNonTermination(
        LLVMSELoop loop,
        List<NonLoopingFormulas> nonLoopingFormulas,
        Set<ExitFormulas> exitFormulas,
        Set<IntegerVariable> interestingRefs,
        Abortion aborter
    ) {
        if (nonLoopingFormulas == null || nonLoopingFormulas.isEmpty() || exitFormulas == null) {
            // there is no path or at least one path has not been handled -> give up
            return null;
        }
        Optional<Node<LLVMAbstractState>> headOptional = loop.getHeadNode();
        if (!headOptional.isPresent()) {
            // no unique head node -> give up
            return null;
        }
        Node<LLVMAbstractState> headNode = headOptional.get();
        LLVMAbstractState headState = headNode.getObject();
        SMTExpression<SBool> invariants = headState.getIntegerState().toRelationSet().toSMTExp();
        List<SMTExpression<SBool>> firstRun = new ArrayList<SMTExpression<SBool>>();
        List<SMTExpression<SBool>> secondRun = new ArrayList<SMTExpression<SBool>>();
        int i = 0;
        final int numOfPaths = nonLoopingFormulas.size();
        while (i < numOfPaths) {
            NonLoopingFormulas formulas = nonLoopingFormulas.get(i);
            firstRun.add(
                Core.and(
                    this.label(formulas.x, i),
                    this.label(formulas.y, i),
                    this.connect(interestingRefs, formulas.z, i, numOfPaths)
                )
            );
            i++;
        }
        for (ExitFormulas formulas : exitFormulas) {
            secondRun.add(Core.and(this.label(formulas.x, numOfPaths), this.label(formulas.y, numOfPaths)));
        }
        SMTExpression<SBool> firstRunFormula = Core.or(firstRun);
        SMTExpression<SBool> nonLoopFormula = Core.and(invariants, firstRunFormula, Core.or(secondRun));
        LLVMProblem.logger.log(Level.FINE, "Non-looping SMT formula: " + nonLoopFormula + ".\n");
        Z3Solver z3 = this.z3factory.getSMTSolver(SMTLIBLogic.QF_NIA, aborter);
        z3.addAssertion(nonLoopFormula);
        if (z3.checkSAT() == YNM.NO) {
            LLVMProblem.logger.fine("Found a non-looping non-terminating loop\n");
            SMTExpression<SBool> witnessFormula = Core.and(invariants, firstRunFormula);
            LLVMAssignmentWitness witness =
                LLVMNonterminationProcessor.computeWitness(
                    loop.getGraph(),
                    loop,
                    headNode,
                    witnessFormula,
                    this.z3factory,
                    aborter
                );
            if (witness == null) {
                LLVMProblem.logger.fine("Could not find a non-looping witness\n");
            }
            return witness;
        }
        LLVMProblem.logger.fine("Could not prove the loop to be non-looping non-terminating\n");
        return null;
    }

    /**
     * The wrapper object for the constructor parameters.
     * These are all part of the LLVMParameters structure.
     * The attributes must be public with default values for the strategy framework.
     * @see LLVMParameters
     */
    public static class Arguments {

        /**
         * Is the original obligation a C program?
         */
        public boolean analyzeC = false;

        /**
         * The SMT solver to use in method calls.
         * NOTE: At this time, Z3 is the only SMT Solver
         * that supports the get-model method, which is needed for
         * nontermination analysis.
         * Hence, this Processor always uses Z3EXT where it has to,
         * regardless of this value.
         */
        public FrontendSMT SMTsolver = FrontendSMT.Z3EXT;

        /**
         * Use bounded or unbounded integer semantics?
         */
        public boolean useBoundedIntegers = false;

        /**
         * Use optimizations to be faster (but maybe weaker)?
         */
        public final boolean useOptimizations = false;

    }

    /**
     * Contains two formulas: The first is a path-based condition and the second the corresponding effect.
     * @author cryingshadow
     * @version $Id$
     */
    public static class ExitFormulas extends Pair<Set<? extends IntegerRelation>, Set<? extends IntegerRelation>> {

        /**
         * For serialization.
         */
        private static final long serialVersionUID = -4805183680581572528L;

        /**
         * @param condition The path-based condition.
         * @param effect The effect along the path.
         */
        public ExitFormulas(Set<? extends IntegerRelation> condition, Set<? extends IntegerRelation> effect) {
            super(condition, effect);
        }

    }

    /**
     * A proof of non-termination.
     * @author Hermann Walth, cryingshadow
     * @version $Id$
     */
    public static class LLVMNonterminationProof extends DefaultProof implements HasGraphmlWitness {

        /**
         * The Graph Problem this processor runs on.
         * Necessary when the processor runs on LLVMProblems directly.
         */
        LLVMSEGraphProblem problem;

        /**
         * The proof for building the SE Graph.
         * Necessary when the processor runs on LLVMProblems directly.
         */
        private Proof priorProof;

        /**
         * A mapping specifying an instance of the SE graph's root node,
         * leading to nontermination
         */
        private LLVMAssignmentWitness witness;

        /**
         * Create a proof from a witness
         * @param priorProof The proof for building the SEGraph.
         * @param problem The Graph Problem this processor runs on.
         * @param witness
         */
        public LLVMNonterminationProof(Proof priorProof, LLVMSEGraphProblem problem, LLVMAssignmentWitness witness) {
            super();
            this.priorProof = priorProof;
            this.problem = problem;
            this.witness = witness;
            assert witness.getNode().equals(problem.getGraph().getRoot()) :
                "Nontermination has to be proven from the start state";
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder res = new StringBuilder();
            if (this.priorProof != null) {
                res.append(this.priorProof.export(o, level));
                res.append(o.newline());
                res.append("LLVM SE Graph Problem:");
                res.append(o.newline());
                res.append(this.problem.export(o));
                res.append(o.newline());
            }
            res.append("Proved nontermination with the following witness:");
            res.append(o.newline());
            res.append(o.preFormatted(this.witness.toString()));
            return res.toString();
        }

        @Override
        public String getGraphmlWitness() {
            return this.witness.getGraphmlWitness();
        }

    }

    /**
     * Contains two formulas: The first is a path-based loop condition and the second the corresponding effect. The
     * third component is a mapping from variables after traversing the path to variables at the beginning of a new
     * path.
     * @author cryingshadow
     * @version $Id$
     */
    public static class NonLoopingFormulas
    extends Triple<Set<IntegerRelation>, Set<IntegerRelation>, Map<IntegerVariable, IntegerVariable>> {

        /**
         * @param condition The path-based loop condition.
         * @param effect The effect along the path.
         * @param correspondence Mapping from variables after path traversal to variables before next path traversal.
         */
        public NonLoopingFormulas(
            Set<IntegerRelation> condition,
            Set<IntegerRelation> effect,
            Map<IntegerVariable, IntegerVariable> correspondence
        ) {
            super(condition, effect, correspondence);
        }

    }
    
    private static EdgeFilter<LLVMEdgeInformation,LLVMAbstractState> doNotUseCallAbstractionOrIntersectionInstantiationFilter = new EdgeFilter<LLVMEdgeInformation, LLVMAbstractState>() {
		@Override
        public boolean selectEdge(Node<LLVMAbstractState> source, Node<LLVMAbstractState> dest, LLVMEdgeInformation label) {
            return !((label instanceof LLVMCallAbstractionEdge) || (label instanceof LLVMIntersectionInstantiationInformation));
        }
	};

}
