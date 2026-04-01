package aprove.input.Programs.llvm.internalStructures.expressions;

import java.util.*;

import aprove.input.Programs.llvm.utils.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;

/**
 * A symbolic variable for LLVM.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMSymbolicVariable extends SymbolicVariable implements LLVMSimpleTerm, IntegerVariable {

    /**
     * Should not be used outside of factory methods (this is why it is package private).
     * @param name The name.
     */
    LLVMSymbolicVariable(String name) {
        this(name, name);
    }

    /**
     * Should not be used outside of factory methods (this is why it is package private).
     * @param name The name.
     * @param dName A name used for debugging purposes (combination of merged variables).
     */
    LLVMSymbolicVariable(String name, String dName) {
        super(name, dName);
    }

    @Override
    public LLVMConstant evaluate(LLVMTermFactory factory) {
        return null;
    }

    @Override
    public Set<? extends LLVMSymbolicVariable> getVariables() {
        return Collections.singleton(this);
    }

    @Override
    public LLVMTerm negate() {
        return LLVMTerm.negate(this, this.getTermFactory());
    }

    @Override
    public String toDOTString() {
        return this.toString();
    }

    @Override
    public String toPrettyString() {
        return this.toString();
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        res.append(this.getName());
        if (LLVMDebuggingFlags.DEBUG_NAMES_IN_OUTPUT) {
            res.append("-");
            res.append(this.getDebugName());
        }
        return res.toString();
    }

    @Override
    public TRSTerm toTerm() {
        return TRSTerm.createVariable(this.getName());
    }

}
