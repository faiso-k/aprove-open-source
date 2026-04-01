package aprove.input.Programs.llvm.processors;

import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.IntegerReasoning.smt.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Builds an SE graph for an LLVM program to prove memory safety.
 * @author cryingshadow
 */
public class LLVMMemorySafetyProcessor extends Processor.ProcessorSkeleton {

    /**
     * Should we use bounded integer semantics or assume unbounded mathematical integers?
     */
    private final boolean bounded;

    /**
     * Should memory leaks be investigated?
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
    public LLVMMemorySafetyProcessor(LLVMMemorySafetyProcessor.Arguments arguments) {
        this.renderGraph = arguments.renderGraph;
        this.solver = arguments.solver;
        this.bounded = arguments.bounded;
        this.useOptimizations = arguments.useOptimizations;
        this.proveFreeOfMemoryLeaks = arguments.proveFreeOfMemoryLeaks;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (obl instanceof LLVMMemSafetyProblem);
    }

    @Override
    public Result process(
        BasicObligation obl,
        BasicObligationNode oblNode,
        Abortion aborter,
        RuntimeInformation rti
    ) throws AbortionException {
        LLVMProblem problem = (LLVMProblem) obl;
        if (LLVMDebuggingFlags.DUMP_SMTLIB) {
            try {
                return ResultFactory.proved(
                    new LLVMMemorySafetyProof(
                        LLVMGraphBuilder.buildGraph(
                            problem.getBasicModule(),
                            problem.getQuery(),
                            new LLVMParameters(
                                problem.wasC(),
                                true,
                                this.proveFreeOfMemoryLeaks,
                                this.bounded,
                                this.useOptimizations,
                                this.solver
                            ),
                            aborter
                        ),
                        this.renderGraph
                    )
                );
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
        } else {
            try {
                return ResultFactory.proved(
                    new LLVMMemorySafetyProof(
                        LLVMGraphBuilder.buildGraph(
                            problem.getBasicModule(),
                            problem.getQuery(),
                            new LLVMParameters(
                                problem.wasC(),
                                true,
                                this.proveFreeOfMemoryLeaks,
                                this.bounded,
                                this.useOptimizations,
                                this.solver
                            ),
                            aborter
                        ),
                        this.renderGraph
                    )
                );
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
    }

    /**
     * Parameters for this processor. Attributes must be public for our strategy framework.
     * @author cryingshadow
     */
    public static class Arguments {

        /**
         * Should we use bounded integer semantics or assume unbounded mathematical integers?
         */
        public boolean bounded = false;

        /**
         * Should memory leaks be investigated?
         */
        public boolean proveFreeOfMemoryLeaks = false;

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
     * Proof for this processor.
     * @author unknown
     */
    public class LLVMMemorySafetyProof extends DefaultProof implements DOT_Able {

        /**
         * Export the graph constructed for this proof?
         */
        private boolean exportGraph;

        /**
         * The graph constructed for this proof.
         */
        private LLVMSEGraph graph;

        /**
         * A constructor is a constructor is a constructor...
         * @param g The graph.
         * @param export Export the graph?
         */
        public LLVMMemorySafetyProof(LLVMSEGraph g, boolean export) {
            super();
            this.exportGraph = export;
            this.graph = g;
        }

        @Override
        public String export(Export_Util eu, VerbosityLevel level) {
            return this.graph.export("Symbolic execution graph based on LLVM program:", this.exportGraph, eu);
        }

        @Override
        public String toDOT() {
            return this.graph.toDOT();
        }

    }

}
