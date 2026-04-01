package aprove.input.Programs.c;

import aprove.input.Programs.llvm.problems.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.*;

/**
 * An obligation for a C program.
 * @author ffrohn
 * @version $Id$
 */
public class CProblem extends DefaultBasicObligation {

    /**
     * The path to the C program.
     */
    private String path;

    /**
     * The query for the C program. Since it is identical to an LLVM query, this type is used here.
     */
    private LLVMQuery query;

    /**
     * @param path The path to the C program.
     * @param query The query for the C program.
     */
    public CProblem(String path, LLVMQuery query) {
        this.path = path;
        this.query = query;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.BasicObligation#getStrategyName()
     */
    @Override
    public String getStrategyName() {
        return "c";
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Export.Utility.Exportable#export(aprove.prooftree.Export.Utility.Export_Util)
     */
    @Override
    public String export(Export_Util eu) {
        return "c file " + this.path;
    }

    /**
     * @return The path to the C program.
     */
    public String getPath() {
        return this.path;
    }

    /**
     * @return The query for the C program.
     */
    public LLVMQuery getQuery() {
        return this.query;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.BasicObligation.DefaultBasicObligation#getName(aprove.verification.dpframework.NameLength)
     */
    @Override
    public String getName(NameLength length) {
        switch (length) {
            case SHORT:
                return "C Problem";
            case LONG:
                return "C " + this.query.getHandlingMode().getName() + " Problem";
            default:
                throw new IllegalStateException("Someone found a new name length...");
        }
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.BasicObligation#getProofPurposeDescriptor()
     */
    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, this.query.getHandlingMode().getName());
    }

}
