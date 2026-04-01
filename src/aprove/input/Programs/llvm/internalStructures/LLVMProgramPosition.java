package aprove.input.Programs.llvm.internalStructures;

import org.json.*;

import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.verification.oldframework.Utility.JSON.*;
import immutables.*;

/**
 * Give a name to program positions (consisting of a function name, a block name, and a line counter within that block).
 * We assume that LLVM functions are not overloaded!
 * @author nowonder, cryingshadow, Frank Emrich
 */
public class LLVMProgramPosition extends ImmutableTriple<String, String, Integer> implements JSONExport {

    /**
     * @param fnName The current function.
     * @param blockName The current block.
     * @param line The current line number within the block.
     */
    public LLVMProgramPosition(String fnName, String blockName, Integer line) {
        super(fnName, blockName, line);
    }

    //TODO doc
    public boolean isFunctionStart(LLVMModule module) {
        LLVMFnDeclaration fnDecl = module.getFunctions().get(this.x);
        if (!(fnDecl instanceof LLVMFnDefinition)) {
            throw new UnsupportedOperationException("We must have a definition of the function");
        }
        return this.y.equals(((LLVMFnDefinition)fnDecl).getNameOfFirstBlock()) && this.z == 0;
    }
    
    public boolean isFirstNonPhiInstruction(LLVMModule module) {
        int firstNonPhiLine = module.getLineOfFirstNonPhiStatement(getFunction(), getBlock());
        return (firstNonPhiLine == getLine());
    }
    
    /**
     * @return True iff this is the first line of the first block of function main
     */
    public boolean isProgramStart(LLVMModule module) {
        return this.getFunction().toString().equals("main") && this.isFunctionStart(module);
    }

    @Override
    public JSONObject toJSON() {
        JSONObject res = new JSONObject();
        res.put("function", this.x);
        res.put("basic_block", this.y);
        res.put("pc", this.z);
        return res;
    }

    public String getFunction() {
        return x;
    }
    
    public String getBlock() {
        return y;
    }
    
    public Integer getLine() {
        return z;
    }
}
