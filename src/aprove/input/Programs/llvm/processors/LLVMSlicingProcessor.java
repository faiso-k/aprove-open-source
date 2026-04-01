package aprove.input.Programs.llvm.processors;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * @author nowonder
 * Builds an SE graph for an LLVM program.
 */
public class LLVMSlicingProcessor extends Processor.ProcessorSkeleton {

    /**
     * Open a browser window to display the symbolic evaluation graph as svg file?
     * (Does not use Firefox, which currently does not feature a search facility.)
     */
    private static final boolean DISPLAY_GRAPH = false;

    /**
     * Render the graph?
     */
    private final LivenessMode liveness;

    /**
     * Full SMT or just simple tricks?
     */
    private final boolean slicing;

    /**
     * @param arguments The parameters of this processor.
     */
    @ParamsViaArgumentObject
    public LLVMSlicingProcessor(final LLVMSlicingProcessor.Arguments arguments) {
        this.slicing = arguments.slicing;
        this.liveness = LivenessMode.valueOf(arguments.liveness);
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.Processor#isApplicable(aprove.prooftree.Obligations.BasicObligation)
     */
    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return (obl instanceof LLVMProblem);
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.Processor#process(aprove.prooftree.Obligations.BasicObligation, aprove.prooftree.Obligations.BasicObligationNode, aprove.strategies.Abortions.Abortion, aprove.strategies.ExecutableStrategies.RuntimeInformation)
     */
    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti
    ) throws AbortionException {
        final LLVMProblem problem = (LLVMProblem) obl;
        final LLVMModule module = problem.getBasicModule();
        final LLVMQuery query = problem.getQuery();
        Map<LLVMProgramPosition, ImmutableSet<String>> liveVariables = module.getLiveVariables();
        if (liveVariables == null) {
            liveVariables = new LinkedHashMap<LLVMProgramPosition, ImmutableSet<String>>();
            final ImmutableSet<String> allVars = ImmutableCreator.create(module.getAllProgramVariableNames());
            for (LLVMProgramPosition pos : module.getAllPositions()) {
                liveVariables.put(pos, allVars);
            }
        }
        //problem.getLiveVariables();
        // build the instruction graph
        final Graph<LLVMLiveness, String> instructionGraph =
            module.computeInstructionGraph(
                new LLVMInstructionGraphNodeObjectCreator<LLVMLiveness>() {

                    @Override
                    public LLVMLiveness create(LLVMModule prog, LLVMProgramPosition pos) {
                        return new LLVMLiveness(pos, module.getInstruction(pos), new LinkedHashSet<String>(), false);
                    }

                }
            );
        // mark all stores and loads as needed, if not slicing then also all returns
        for (final LLVMLiveness live : instructionGraph.getNodeObjects()) {
            if (
                live.x instanceof LLVMLoadInstruction
                || live.x instanceof LLVMStoreInstruction
                // FIXME I guess this is wrong - here, we just need ret instructions, don't we?
                || (!this.slicing && live.x instanceof LLVMTerminatorInstruction)
            ) {
                live.z = true;
            }
        }
        // mark branch instructions on SCCs as needed
        final SCCGraph<LLVMLiveness, String> justSccGraph = new SCCGraph<LLVMLiveness, String>(instructionGraph, true, true);
        for (final Cycle<LLVMLiveness> scc : justSccGraph.getNodeObjects()) {
            for (final LLVMLiveness live : scc.getNodeObjects()) {
                if (live.x instanceof LLVMBranchInstruction) {
                    live.z = true;
                }
            }
        }
        // perform backwards analysis (marking as needed what computes live variables)
        // if not liveness, then all predecessors are needed and all variables are live (reuse liveVariables from
        // original llvmproblem)
        final SCCGraph<LLVMLiveness, String> sccGraph = new SCCGraph<LLVMLiveness, String>(instructionGraph, false, false);
        for (final Cycle<LLVMLiveness> rank : sccGraph.getRankedSCCs()) {
            String old;
            do {
                old = rank.size() > 1 ? instructionGraph.toDOT() : "";
                for (final Node<LLVMLiveness> node : rank) {
                    final LLVMLiveness live = node.getObject();
                    if (this.liveness == LivenessMode.OFF) {
                        live.y.addAll(liveVariables.get(live.w));
                        if (!live.z) {
                            for (final Node<LLVMLiveness> succ : instructionGraph.getOut(node)) {
                                if (succ.getObject().z) {
                                    live.z = true;
                                    break;
                                }
                            }
                        }
                        continue;
                    }
                    final boolean isBranch = live.x instanceof LLVMBranchInstruction;
                    final Set<String> vars = live.y;
                    for (final Node<LLVMLiveness> succ : instructionGraph.getOut(node)) {
                        final LLVMLiveness succLive = succ.getObject();
                        vars.addAll(succLive.y);
                        if (!live.z && isBranch) {
                            final String blockName = succLive.w.y;
                            Node<LLVMLiveness> current = succ;
                            while (current != null && current.getObject().w.y.equals(blockName)) {
                                if (current.getObject().z) {
                                    live.z = true;
                                    break;
                                }
                                final Iterator<Node<LLVMLiveness>> i = instructionGraph.getOut(current).iterator();
                                current = i.hasNext() ? i.next() : null;
                            }
                        }
                    }
                    live.z = live.z || vars.contains(live.x.getProducedVariable());
                    if (live.z) {
                        switch (this.liveness) {
                            case SCC:
                                live.x.collectVariables(vars);
                                break;
                            case FULL:
                                live.x.addConeVariables(vars);
                                break;
                            case OFF:
                                // do nothing
                        }
                    }
                }
            } while (rank.size() > 1 ? !instructionGraph.toDOT().equals(old) : false);
        }

        if (LLVMSlicingProcessor.DISPLAY_GRAPH) {
            DisplayGraph.display(instructionGraph.toDOT());
        }
        // finally remove unneeded instructions
        // i.e., all instructions with !needed
        // make sure there is some ret terminating instruction at the end of the block
        final DoubleMap<String, String, Set<Integer>> toRemove = new DoubleMap<String, String, Set<Integer>>();
        if (this.liveness != LivenessMode.OFF) {
            liveVariables = new LinkedHashMap<LLVMProgramPosition, ImmutableSet<String>>();
        }
        for (final LLVMLiveness live : instructionGraph.getNodeObjects()) {
            final LLVMProgramPosition pos = live.w;
            if (this.liveness != LivenessMode.OFF) {
                // save live variables in mapping
                liveVariables.put(pos, ImmutableCreator.create(live.y));
            }
            if (!live.z) {
                Set<Integer> lines = toRemove.get(pos.x, pos.y);
                if (lines == null) {
                    lines = new LinkedHashSet<Integer>();
                    toRemove.put(pos.x, pos.y, lines);
                }
                lines.add(pos.z);
            }
        }
        Map<String, LLVMFnDeclaration> newFunctions;
        if (toRemove.keySet().isEmpty()) {
            newFunctions = module.getFunctions();
        } else {
            newFunctions = new LinkedHashMap<String, LLVMFnDeclaration>();
            for (final Map.Entry<String, LLVMFnDeclaration> functionEntry : module.getFunctions().entrySet()) {
                final String functionName = functionEntry.getKey();
                LLVMFnDeclaration functionDecl = functionEntry.getValue();
                if (toRemove.keySet().contains(functionName)) {
                    final LLVMFnDefinition functionDef = (LLVMFnDefinition) functionDecl;
                    final Map<String, LLVMBasicBlock> newBlocks = new LinkedHashMap<String, LLVMBasicBlock>();
                    for (final Map.Entry<String, LLVMBasicBlock> blockEntry : functionDef.getBlocks().entrySet()) {
                        final String blockName = blockEntry.getKey();
                        LLVMBasicBlock block = blockEntry.getValue();
                        if (toRemove.get(functionName).keySet().contains(blockName)) {
                            final Set<Integer> remove = toRemove.get(functionName, blockName);
                            final List<LLVMInstruction> newList = new ArrayList<LLVMInstruction>();
                            final ImmutableList<LLVMInstruction> list = block.getInstructions();
                            int j = 0;
                            for (int i = 0; i < list.size(); i++) {
                                final LLVMProgramPosition oldPos = new LLVMProgramPosition(functionName, blockName, i);
                                final LLVMProgramPosition newPos = new LLVMProgramPosition(functionName, blockName, j);
                                final ImmutableSet<String> liveVars = liveVariables.remove(oldPos);
                                if (!remove.contains(i)) {
                                    newList.add(list.get(i));
                                    liveVariables.put(newPos, liveVars);
                                    j++;
                                }
                            }
                            if (newList.isEmpty() || !(newList.get(newList.size()-1) instanceof LLVMTerminatorInstruction)) {
                                try {
                                    newList.add(
                                        new LLVMRetInstruction(functionDef
                                            .getReturnType()
                                            .getType()
                                            .convertToZeroInitializedLiteral(false),
                                        -1)
                                    );
                                    liveVariables.put(
                                        new LLVMProgramPosition(functionName, blockName, newList.size()-1),
                                        ImmutableCreator.create(Collections.<String>emptySet()));
                                } catch (final LLVMParseException e) {
                                    return ResultFactory.error(e);
                                }
                            }
                            final LLVMBasicBlock newBlock = new LLVMBasicBlock(blockName, ImmutableCreator.create(newList));
                            block = newBlock;
                        }
                        newBlocks.put(blockName, block);
                    }
                    final LLVMFnDefinition newFunctionDef =
                        new LLVMFnDefinition(functionDef, ImmutableCreator.create(newBlocks));
                    functionDecl = newFunctionDef;
                }
                newFunctions.put(functionName, functionDecl);
            }
        }
        return
            ResultFactory.proved(
                LLVMProblem.create(
                    module.setFunctions(newFunctions).setLiveVariables(liveVariables),
                    query,
                    problem.wasC(),
                    problem.getFileToRemove()
                ),
                // TODO why complete?
                YNMImplication.COMPLETE,
                new LLVMSlicingProof()
            );
    }

    /**
     * @author unknown
     * Parameters for this processor.
     */
    public static class Arguments {

        /**
         * Perform live variable analysis.
         */
        public String liveness = "FULL";
        // CHECKSTYLE.ON: ExplicitInitialization
        // CHECKSTYLE.ON: VisibilityModifier

        // CHECKSTYLE.OFF: ExplicitInitialization
        // it is so simple here that an additional constructor would just be overhead
        // CHECKSTYLE.OFF: VisibilityModifier
        // this visibility is needed for our strategy
        /**
         * Remove unnecessary statements.
         */
        public boolean slicing = true;

    }

    // TODO document me
    public static enum LivenessMode {
        FULL, OFF, SCC
    }

    /**
     * @author unknown
     * Proof for this processor.
     * TODO add meaningful messages
     */
    public class LLVMSlicingProof extends DefaultProof {

        /**
         * A constructor is a constructor is a constructor...
         */
        public LLVMSlicingProof() {
            super();
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Utility.VerbosityExportable#export(aprove.prooftree.Export.Utility.Export_Util, aprove.verification.oldframework.Utility.VerbosityLevel)
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "";
        }

    }

}
