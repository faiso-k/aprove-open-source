package aprove.input.Programs.llvm.processors;

import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.IntegerReasoning.smt.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.xml.*;
import immutables.*;

import java.util.Map;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

/**
 * @author unknown, CryingShadow
 * Builds an SE graph for an LLVM program.
 */
public class LLVMToSEGraphProcessor extends Processor.ProcessorSkeleton {

    /**
     * Should we use bounded integer semantics or assume unbounded mathematical integers?
     */
    private final boolean bounded;

    /**
     * Prove memory safety or assume it?
     */
    private final boolean proveMemorySafety;

    /**
     * Investigate memory leaks?
     */
    private final boolean proveFreeOfMemoryLeaks;

    /**
     * Render the graph?
     */
    private final boolean renderGraph;

    /**
     * Use optimizations to be faster (but maybe weaker)?
     */
    public final boolean useOptimizations;

    /**
     * The SMT solver to use.
     */
    private final FrontendSMT solver;

    /**
     * @param arguments The parameters of this processor.
     */
    @ParamsViaArgumentObject
    public LLVMToSEGraphProcessor(LLVMToSEGraphProcessor.Arguments arguments) {
        this.renderGraph = arguments.renderGraph;
        this.solver = arguments.solver;
        this.proveMemorySafety = arguments.proveMemorySafety;
        this.bounded = arguments.bounded;
        this.useOptimizations = arguments.useOptimizations;
        this.proveFreeOfMemoryLeaks = arguments.proveFreeOfMemoryLeaks;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (obl instanceof LLVMProblem);
    }

    @Override
    public Result process(
        BasicObligation obl,
        BasicObligationNode oblNode,
        Abortion aborter,
        RuntimeInformation rti
            ) throws AbortionException {
        LLVMProblem problem = (LLVMProblem)obl;
        try {
            LLVMParameters parameters = new LLVMParameters(
                                                           problem.wasC(),
                                                           this.proveMemorySafety,
                                                           this.proveFreeOfMemoryLeaks,
                                                           this.bounded,
                                                           this.useOptimizations,
                                                           this.solver
                    );
            LLVMSEGraph graph = LLVMGraphBuilder.buildGraph(problem.getBasicModule(), problem.getQuery(), parameters, aborter);
            LLVMSEGraphProblem graphProblem = new LLVMSEGraphProblem(graph, this.renderGraph);
            graphProblem.setParent(obl);  // LLVM problem is the parent of LLVM SE graph problem
            graphProblem.setVariableRenaming(getVariableRenamingFromGraph(graph));

            return ResultFactory.proved(graphProblem, YNMImplication.EQUIVALENT, new LLVMToTerminationGraphProof(this.proveMemorySafety));
        } catch (
            MemorySafetyException
            | UndefinedBehaviorException
            | AssertionException
            | ErrorStateException
            | MemoryLeakException e
        ) {
            System.err.println(e.getMessage());
            return ResultFactory.unsuccessful(e.getMessage());
        } finally {
            problem.cleanUp();
        }
    }

    /**
     * Get variable renaming from LLVM SE graph
     *
     * @param graph
     */
    private CollectionMap<String, String> getVariableRenamingFromGraph(LLVMSEGraph graph) {
        final CollectionMap<String, String> result = new CollectionMap<>();

        // iterate over all nodes in resulting symbolic execution graph
        for (Node<LLVMAbstractState> node : graph.getNodes()) {

            // LLVM abstract state associated with current node should not be null
            assert node.getObject() != null;

            // get and iterate over all variable mapping associated with current LLVM abstract state
            for (Map.Entry<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> entry : node.getObject().getProgramVariables().entrySet()) {
                // save variable mapping
                if (!(entry.getValue().x instanceof LLVMHeuristicConstRef)) {
                    result.add(entry.getKey(), entry.getValue().x.getName());
                }
            }
        }

        return result;
    }

    /**
     * Parameters for this processor. Attributes must be public for our strategy framework.
     * @author cryingshadow
     */
    public static class Arguments {

        /**
         * Investigate for memory leaks?
         */
        public boolean proveFreeOfMemoryLeaks = false;

        /**
         * Should we use bounded integer semantics or assume unbounded mathematical integers?
         */
        public boolean bounded = false;

        /**
         * Prove memory safety or assume it?
         */
        public boolean proveMemorySafety = true;

        /**
         * Render the graph?
         */
        public boolean renderGraph = false;

        /**
         * Use optimizations to be faster (but maybe weaker)?
         */
        public boolean useOptimizations = false;

        /**
         * The SMT solver to use.
         */
        public FrontendSMT solver = FrontendSMT.HEURISTICS;

    }

    /**
     * @author unknown, cryingshadow
     * Proof for this processor.
     * TODO add meaningful messages
     */
    public class LLVMToTerminationGraphProof extends DefaultProof {

        /**
         * Flag indicating whether construction of the SE graph proved memory safety.
         */
        private final boolean provedMemSafety;

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {

            return CPFTag.LLVM_SEG_PROOF.create(doc);
        }


        /**
         * A constructor is a constructor is a constructor...
         * @param memSafety Flag indicating whether construction of the SE graph proved memory safety.
         */
        public LLVMToTerminationGraphProof(boolean memSafety) {
            super();
            this.provedMemSafety = memSafety;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return
                "Constructed symbolic execution graph for LLVM program"
                + (this.provedMemSafety ? " and proved memory safety." : ".");
        }
    }

}
