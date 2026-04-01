package aprove.input.Programs.llvm.internalStructures;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.IntegerReasoning.smt.*;

/**
 * Strategy parameters for the LLVM frontend.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMParameters {
    /**
     * Is the original obligation a C program? In that case, some behavior which is defined in LLVM is treated as
     * undefined behavior according to the C standard.
     */
    public final boolean analyzeC;

    /**
     * Should memory safety be proved during graph construction?
     */
    public final boolean proveMemorySafety;

    /**
     * Should be proved during graph construction that the program does not contain memory leaks?
     */
    public final boolean proveFreeOfMemoryLeaks;

    /**
     * The SMT solver to use for the LLVM frontend.
     */
    public final FrontendSMT SMTsolver;

    /**
     * Use bounded or unbounded integer semantics?
     */
    public final boolean useBoundedIntegers;

    /**
     * Use optimizations to be faster (but maybe weaker)?
     */
    public final boolean useOptimizations;

    /**
     * Strategy parameters for LLVM frontend.
     * @param c Is the original obligation a C program? In that case, some behavior which is defined in LLVM is treated
     *          as undefined behavior according to the C standard.
     * @param proveMemSafety Should memory safety be proved during graph construction?
     * @param proveFreeOfMemoryLeaks Should the program be proved to be free of memory leaks during graph construction?
     * @param bounded Use bounded or unbounded integer semantics?
     * @param optimizations Use optimizations to be faster (but maybe weaker)?
     * @param smt The SMT solver to use for the LLVM frontend.
     */
    public LLVMParameters(
        boolean c,
        boolean proveMemSafety,
        boolean proveFreeOfMemoryLeaks,
        boolean bounded,
        boolean optimizations,
        FrontendSMT smt
    ) {
        this.analyzeC = c;
        this.proveMemorySafety = proveMemSafety;
        this.proveFreeOfMemoryLeaks = proveFreeOfMemoryLeaks;
        this.useBoundedIntegers = bounded;
        this.useOptimizations = optimizations;
        this.SMTsolver = smt;
    }

}
