package aprove.input.Programs.llvm.processors;

import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.IntegerReasoning.smt.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author unknown, CryingShadow
 * Builds an SE graph for an LLVM program.
 */
public class LLVMToCpxGraphProcessor extends Processor.ProcessorSkeleton {

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
    public LLVMToCpxGraphProcessor(LLVMToCpxGraphProcessor.Arguments arguments) {
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
            LLVMComplexityGraphProblem graphProblem = new LLVMComplexityGraphProblem(graph, this.renderGraph);
            return ResultFactory.proved(graphProblem, UpperBound.create(), new LLVMToComplexityGraphProof(this.proveMemorySafety));
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
        public final boolean useOptimizations = false;

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
    public class LLVMToComplexityGraphProof extends DefaultProof {

        /**
         * Flag indicating whether construction of the SE graph proved memory safety.
         */
        private final boolean provedMemSafety;

        /**
         * A constructor is a constructor is a constructor...
         * @param memSafety Flag indicating whether construction of the SE graph proved memory safety.
         */
        public LLVMToComplexityGraphProof(boolean memSafety) {
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
