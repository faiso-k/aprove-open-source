package aprove.input.Programs.llvm.internalStructures.module;

import immutables.*;

/**
 * @author Jera Hensel
 */
public class LLVMDebugInformation implements Immutable {
    
    private final int index;

    private final String functionName;
    
    private final int cLine;

    public LLVMDebugInformation(int index, String name, int line)
    {
        this.index = index;
        this.functionName = name;
        this.cLine = line;
    }
    
    public int getCLine() {
        return this.cLine;
    }
    
    public String getFunctionName() {
        return this.functionName;
    }
    
    public int getIndex() {
        return this.index;
    }

}
