package aprove.input.Programs.llvm.internalStructures;

/**
 * A witness that starts a nonterminating loop.
 * @author jhensel
 */
public class LLVMWitness {

    /**
     * The path through the C program in the GraphML format.
     */
    private String pathThroughProgram;

    /**
     * Create a simple witness representing a path through the C program.
     * @param graphmlPath The path through the C program in GraphML
     */
    public LLVMWitness(String graphmlPath) {
        this.pathThroughProgram = graphmlPath;
    }
    
    public String getGraphmlWitness() {
        return this.pathThroughProgram;
    }

}
