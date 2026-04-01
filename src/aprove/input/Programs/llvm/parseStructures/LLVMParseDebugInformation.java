package aprove.input.Programs.llvm.parseStructures;

import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.parseStructures.literals.*;

public class LLVMParseDebugInformation {
    
    private LLVMParseLiteral index;
    
    private String functionName;
    
    private LLVMParseLiteral cLine;

    public LLVMDebugInformation convertToDebugInformation(int pointerSize)
    throws LLVMParseException {
        return
            new LLVMDebugInformation(
                this.index.convertToI32(pointerSize),
                this.functionName,
                this.cLine == null? -1 : this.cLine.convertToI32(pointerSize)
            );
    }
    
    public LLVMParseLiteral getcLine() {
        return this.cLine;
    }
    
    public String getFunctionName() {
        return this.functionName;
    }
    
    public LLVMParseLiteral getIndex() {
        return this.index;
    }
    
    public void setCLine(LLVMParseLiteral line) {
        this.cLine = line;
    }
    
    public void setFunctionName(String fname) {
        this.functionName = fname;
    }
    
    public void setIndex(LLVMParseLiteral index) {
        this.index = index;
    }
    
}
