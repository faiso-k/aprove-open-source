package aprove.input.Programs.llvm.utils;

import java.io.*;

/**
 * Class holding debugging flags.
 * @author CryingShadow
 */
public abstract class LLVMDebuggingFlags {

    /**
     * Add changing relations during formula update to edges?
     */
    public static final boolean ADD_CHANGES_DURING_FORMULA_UPDATE_TO_EDGES = false;

    /**
     * Even if we do not remove unused parts from the graph, we can display the node used for generalization directly
     * at the generalization edge.
     */
    public static final boolean ALWAYS_SHOW_NODE_USED_FOR_GENERALIZATION = true;

    /**
     * Should the invariants on states etc. be checked during runtime?
     */
    public static final boolean CHECK_INVARIANTS = true;

    /**
     * Output debug names for references to follow merges.
     */
    public static final boolean DEBUG_NAMES_IN_OUTPUT = false;

    /**
     * Should the SMT problems be dumped as SMTLIB files?
     */
    public static final boolean DUMP_SMTLIB = false;

    /**
     * The folder where to store the SMTLIB files dumped from the SMT problems.
     */
    public static final String DUMP_SMTLIB_FOLDER = "D:\\Test\\SMT";

    /**
     * Should the dot-graph be clustered by the currently active function (FunctionGraph)?
     */
    public static final boolean GROUP_SEGRAPH_BY_FUNCTION_IN_DOT_OUTPUT = false;

    /**
     * Output all states during symbolic evaluation.
     */
    public static final boolean OUTPUT_ALL_STATES = false;

    /**
     * Output the whole graph after it has been generated
     * Should be false for benchmarking/competitions!
     */
    public static final boolean OUTPUT_FINAL_GRAPH = false;
    
    /**
     * Output the whole graph during symbolic evaluation after each nth step (0 means no output).
     * Should be 0 for benchmarking/competitions!
     */
    public static final int OUTPUT_GRAPH_AFTER_EACH_NTH_STEP = 0;
    
    /**
    * Output some debug info (time, number of states in graph) to STDERR  during symbolic execution after each nth step (0 means no output).
    * Should be 0 for benchmarking/competitions!
    */
   public static final int OUTPUT_DEBUG_INFO_AFTER_EACH_NTH_STEP = 0;

   /**
    * Should we compact the graph (i.e., combine sequences without branching into a single edge) whenever we dump the graph?
    */
   public static final boolean COMPACT_GRAPH_BEFORE_OUTPUT = false;
   
    /**
     * Output the JSON export of the graph during symbolic execution after each step.
     */
    public static final boolean OUTPUT_JSON_AFTER_EACH_STEP = false;

    /**
     * Additionally show all generated rules after simplification on stderr.
     */
    public static final boolean OUTPUT_RULES_AFTER_SIMPLIFICATION = false;

    /**
     * Additionally show all generated rules before simplification on stderr.
     */
    public static final boolean OUTPUT_RULES_BEFORE_SIMPLIFICATION = false;

    /**
     * Remove parts from the graph where a generalization repeats the evaluation in a more general way.
     */
    public static final boolean REMOVE_TOO_CONCRETE_PARTS_FROM_GRAPH = true;

    /**
     * Still return the unfinished graph after occurrence of an exception.
     * Should be false for benchmarking/competitions!
     */
    public static final boolean RETURN_GRAPH_AFTER_EXCEPTION = true;

    /**
     * Switch for SV-COMP mode. Accepts files without queries and creates a query for main() then. Moreover, calls to
     * functions called __VERIFIER_nondet_String without arguments are treated in a special way.
     */
    public static final boolean SV_COMP_MODE = true;

    /**
     * Switch for termCOMP mode. Accepts files without queries and creates a query for main() then. Moreover, calls to
     * functions called __VERIFIER_nondet_String without arguments are treated in a special way.
     */
    public static final boolean TERMCOMP_MODE = false;

    /**
     * Throw assertion exceptions in case of specified assertion calls?
     */
    public static final boolean USE_ASSERTION_EXCEPTIONS = false;

    /**
     * Throw error exceptions when reaching an error statement?
     */
    public static final boolean USE_ERROR_LOCATIONS = false;

    /**
     * Use HTML layout for DOT outputs or the old one?
     */
    public static final boolean USE_HTML_DOT_LAYOUT = false;

    /**
     * Use restriction to used references?
     */
    public static final boolean USE_RESTRICTION_TO_USED_REFS = true;
    
    
    /**
     * When using <code>LLVMFunctionGraph</code>, shall we check each time we use one of the shadowed data structures
     * if they are in sync with the underlying LLMSEGraph?
     */
    public static final boolean PERFORM_SLOW_FUNCTION_GRAPH_CONSISTENCY_CHECKS = false;

    /**
     * Shall we check the consisteny of all <code>LLVMFunctionGraph</code>s after each
     * graph construction step
     */
    public static final boolean CHECK_FUNCTION_GRAPH_CONSISTENCY_AFTER_EACH_ITERATION = false;
    
    
    /**
     * Should we cache the results of the evaluators that act on execution paths used 
     * for state intersection/function summarization?
     */
    public static final boolean CACHE_INTERSECTION_PATH_EVALUATOR_RESULTS = true;

    
    /**
     * Performs some additional consistency checks at the end of graph construction.
     * These must only be satisfied if the program terminates, must therefore be disabled by default.
     * (otherwise, we would fail on some non-terminating functions)
     */
    public static final boolean PERFORM_GRAPH_CONSISTENCY_CHECKS_FOR_TERMINATING_FUNCTIONS = false;
    
    
    /**
     * @return A fresh file in a special folder for dumping SMTLIB problems.
     * @throws IOException If an I/O error occurs.
     */
    public static File getNextSMTLIBDumpFile() throws IOException {
        File folder = new File(LLVMDebuggingFlags.DUMP_SMTLIB_FOLDER);
        if (!folder.exists()) {
            if (!folder.mkdir()) {
                throw new IOException("Could not create folder!");
            }
        }
        File id = new File(LLVMDebuggingFlags.DUMP_SMTLIB_FOLDER + File.separator + "id.txt");
        final int next;
        if (id.exists()) {
            try (BufferedReader reader = new BufferedReader(new FileReader(id))) {
                next = Integer.parseInt(reader.readLine());
            }
        } else {
            next = 1;
        }
        final int cut = 10000;
        String problemFolder = "" + (next / cut);
        String number = "" + (next % cut);
        while (number.length() < 4) {
            number = "0" + number;
        }
        while (problemFolder.length() < 5) {
            problemFolder = "0" + problemFolder;
        }
        try (FileWriter writer = new FileWriter(id)) {
            writer.write("" + (next + 1));
        }
        StringBuilder path = new StringBuilder();
        path.append(LLVMDebuggingFlags.DUMP_SMTLIB_FOLDER);
        path.append(File.separator);
        path.append(problemFolder);
        File problemDirectory = new File(path.toString());
        if (!problemDirectory.exists()) {
            problemDirectory.mkdir();
        }
        path.append(File.separator);
        path.append(number);
        path.append(".smt2");
        return new File(path.toString());
    }

    /**
     * Hide default constructor.
     */
    private LLVMDebuggingFlags() {
        throw new UnsupportedOperationException("Do not instantiate me!");
    }

}
