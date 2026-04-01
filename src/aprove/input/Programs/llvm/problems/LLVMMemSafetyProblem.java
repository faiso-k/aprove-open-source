package aprove.input.Programs.llvm.problems;

import java.io.*;

import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;

/**
 * An LLVM problem to be analyzed for memory safety.
 * @author ffrohn, cryingshadow
 * @version $Id$
 */
public class LLVMMemSafetyProblem extends LLVMProblem {

    /**
     * @param basicModuleParam The LLVM program.
     * @param queryParam The starting query.
     * @param fromC Is the LLVM program used to actually analyze a C program?
     * @param fileToRemove {@link LLVMProblem#getFileToRemove()}
     */
    protected LLVMMemSafetyProblem(
        LLVMModule basicModuleParam,
        LLVMQuery queryParam,
        boolean fromC,
        File fileToRemove
    ) {
        super(basicModuleParam, queryParam, fromC, fileToRemove);
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Memory Safety");
    }

    @Override
    public String getStrategyName() {
        return "llvmMemSafety";
    }

    @Override
    public LLVMProblem setFileToRemove(File fileToRemove) {
        return new LLVMMemSafetyProblem(this.getBasicModule(), this.getQuery(), this.wasC(), fileToRemove);
    }

    @Override
    public LLVMProblem setFromC() {
        return new LLVMMemSafetyProblem(this.getBasicModule(), this.getQuery(), true, this.getFileToRemove());
    }

}
