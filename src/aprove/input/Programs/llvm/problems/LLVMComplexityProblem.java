package aprove.input.Programs.llvm.problems;

import java.io.*;

import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;

/**
 * An LLVM problem to be analyzed for termination.
 * @author ffrohn, cryingshadow
 * @version $Id$
 */
public class LLVMComplexityProblem extends LLVMProblem {

    /**
     * @param basicModuleParam The LLVM program.
     * @param queryParam The starting query.
     * @param liveVariablesParam A mapping from program positions to sets of variable names of live variables.
     * @param fromC Is the LLVM program used to actually analyze a C program?
     * @param fileToRemove {@link LLVMProblem#getFileToRemove()}
     */
    protected LLVMComplexityProblem(
        LLVMModule basicModuleParam,
        LLVMQuery queryParam,
        boolean fromC,
        File fileToRemove
    ) {
        super(basicModuleParam, queryParam, fromC, fileToRemove);
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Complexity");
    }

    @Override
    public String getStrategyName() {
        return "llvmComplexity";
    }

    @Override
    public LLVMProblem setFileToRemove(File fileToRemove) {
        return new LLVMComplexityProblem(this.getBasicModule(), this.getQuery(), this.wasC(), fileToRemove);
    }

    @Override
    public LLVMProblem setFromC() {
        return new LLVMComplexityProblem(this.getBasicModule(), this.getQuery(), true, this.getFileToRemove());
    }

}
