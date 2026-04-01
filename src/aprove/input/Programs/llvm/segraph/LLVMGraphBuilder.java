package aprove.input.Programs.llvm.segraph;

import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.strategies.Abortions.*;

/**
 * Class which builds the full termination graph from an LLVM program.
 * @author Janine Repke, cryingshadow
 */
public final class LLVMGraphBuilder {

    /**
     * @param basicModule The LLVM module.
     * @param query The starting query.
     * @param debug Flag indicating whether or not to output debug information.
     * @param params Strategy parameters.
     * @return A symbolic evaluation graph for the specified module and query.
     * @throws MemorySafetyException If memory safety of the program cannot be proven by the construction of this graph.
     * @throws UndefinedBehaviorException If it cannot be proven that the program behavior is sufficiently defined.
     * @throws AssertionException If satisfaction of all assertions cannot be proven by the construction of this graph.
     * @throws ErrorStateException If an error state is reached.
     * @throws MemoryLeakException If the program contains a memory leak.
     */
    public static LLVMSEGraph buildGraph(
        LLVMModule basicModule,
        LLVMQuery query,
        boolean debug,
        LLVMParameters params,
        Abortion aborter
    ) throws
        MemorySafetyException,
        UndefinedBehaviorException,
        AssertionException,
        ErrorStateException,
        MemoryLeakException
    {
        // create termination graph with only one root state
        LLVMSEGraph termGraph = new LLVMSEGraph(basicModule, query, params, aborter);
        if (LLVMDebuggingFlags.RETURN_GRAPH_AFTER_EXCEPTION) {
            try {
                termGraph.buildFullGraph(debug, aborter);
                // CHECKSTYLE.OFF: IllegalCatch
                // We really want to change the output behavior for arbitrary exceptions here
            } catch (Exception e) {
                // CHECKSTYLE.ON: IllegalCatch
                e.printStackTrace(System.err);
                return termGraph;
            }
        } else {
            termGraph.buildFullGraph(debug, aborter);
        }
        return termGraph;
    }

    /**
     * @param basicModule The LLVM module.
     * @param query The starting query.
     * @param params Strategy parameters.
     * @return A symbolic evaluation graph for the specified module and query.
     * @throws MemorySafetyException If memory safety of the program cannot be proven by the construction of this graph.
     * @throws UndefinedBehaviorException If it cannot be proven that the program behavior is sufficiently defined.
     * @throws AssertionException If satisfaction of all assertions cannot be proven by the construction of this graph.
     * @throws ErrorStateException If an error state is reached.
     * @throws MemoryLeakException If the program contains a memory leak.
     */
    public static LLVMSEGraph buildGraph(LLVMModule basicModule, LLVMQuery query, LLVMParameters params, Abortion aborter)
    throws
        MemorySafetyException,
        UndefinedBehaviorException,
        AssertionException,
        ErrorStateException,
        MemoryLeakException
    {
    	
        // create termination graph with only one root state
        LLVMSEGraph termGraph = new LLVMSEGraph(basicModule, query, params, aborter);
        
        try {
        // evaluate all states
        termGraph.buildFullGraph(aborter);
        
        if (LLVMDebuggingFlags.OUTPUT_FINAL_GRAPH) {
            termGraph.dumpGraph();
        }
    	} catch (MemorySafetyException |
    	        UndefinedBehaviorException |  
    	        AssertionException |
    	        ErrorStateException |
    	        MemoryLeakException e) {
    		if(termGraph != null && LLVMDebuggingFlags.RETURN_GRAPH_AFTER_EXCEPTION) {
    			termGraph.dumpGraph();
    		}
    		throw e;
    	}
        
        return termGraph;
    }

    /**
     * Hides the default constructor.
     */
    private LLVMGraphBuilder() {
        // hides the default constructor
    }

}
