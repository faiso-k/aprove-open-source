package aprove.input.Programs.llvm.utils;

/**
 * Convert LLVM object into proper LLVM IR expression
 * @author Max Haslbeck
 */
public interface LLVMIRExport {
	/**
	 * Returns a string that is a valid LLVM IR instruction. That means the string
	 * is a valid line in a LLVM IR block statement. The returned string is not
	 * indented.
	 * 
	 * @return String that is a valid LLVM IR instruction
	 */
    public String toLLVMIR();
}