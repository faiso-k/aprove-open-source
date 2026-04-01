package aprove.input.Programs.llvm.processors;


public interface HasGraphmlWitness {

    /**
     * @return A path through the C program in the GraphML format.
     */
    public abstract String getGraphmlWitness();
    
}
