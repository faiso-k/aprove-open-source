package aprove.verification.dpframework.MCSProblem.mcnp;

import aprove.verification.dpframework.MCSProblem.mcnp.Constants.*;

public class Config {

    // Display MCGs and LevelMappings
    public static boolean GRAPHICS = false;

    // ==================== Logger =======================
    // There are 3 levels of logs, each one is written to appropriate file
    // in the current working directory (report.log, output.log,debug.log).
    // Report is highest level, output - middle, debug - the lowest.
    // Report logs are added to the existing report.log file and two others
    // deletes the existing file and create new ones in  e3very run.

    // Which log level to print into stdout: 3 - debug, 2 - output, 1 - report, 0 - nothing
    private static int LOGGER_LEVEL = 2;

    // do not write debug level log (not to file and not to debug.log file)
    public static boolean DEBUG_LOG = false;
    public static final boolean OVERRIDE_LOG_FILES = true;
    public static final boolean PRINT_LOG = false;
    // enable/disable part of the log
    public static final boolean LOG_READING_INPUT = false;
    public static final boolean LOG_BUILDING_SCC = false;
    public static final boolean LOG_ENCODING = false;
    public static final boolean LOG_LEVEL_MAPPINGS_SEARCH = false;
    public static final boolean LOG_LEVEL_MAPPINGS_RESULT = false;
    public static final boolean LOG_MERGING_GRAPHS = false;
    public static final boolean LOG_TIMES = false;
    public static final boolean LOG_VERIFICATION = false;


    // ======================= Configuration =====================
    // do transitive closure for MC graphs
    public static final boolean MC_TRANSITIVE_CLOSURE = true;
    // if the value is false, will try only taged level mappings
    public static final boolean TRY_PLAIN_LEVEL_MAPPING = false;
    // numbers encoding method (for future use - only unary was used)
    public static final UnaryBinary NUMBERS_ENCODING = Constants.UnaryBinary.UNARY;
    // checks that ranking function is correct (used in Main.java). Used for debugging.
    public static final boolean VERIFICATION = false;
    //call garbage collector each time before running SAT solver
    public static final boolean CALL_GC = false;
    //merge graphs having one one entering or exiting edge.
    //Now it is not used since the procedure uis done in preprocessing stage (not in this code)
    public static final boolean MERGE_GRAPHS = false;



    // ==============================================================
    // The following variables were used during the development.
    // Some of them may be canceled later.
    // ==============================================================
    //add variables are in high or low set
    public static final boolean USE_ALL_ARGS = false;
    //low and high sets may intersect
    public static final boolean HIGH_LOW_MAY_INTERSECT = true;
    //both high and low sets have to include at least one variable
    public static final boolean HIGH_LOW_NOT_EMPTY = true;
    //were used for backward compatibility. Does not work anymore. Don't change the values.
    public static final boolean CUTSET_METHOD = true;
    public static final boolean CUTSET_METHOD_2 = true;

    public static final String[] GRAPHS_ORDERING_TYPES = {
        //min/max , min/max
        Constants.GRAPH_SW_MAX_MAX_MAX_ORDERING, Constants.GRAPH_WS_MAX_MAX_MAX_ORDERING,

        Constants.GRAPH_SW_MIN_MIN_MIN_ORDERING, Constants.GRAPH_WS_MIN_MIN_MIN_ORDERING,

        Constants.GRAPH_SW_MIN_MAX_MAXMIN_ORDERING, Constants.GRAPH_WS_MIN_MAX_MAXMIN_ORDERING,

        Constants.GRAPH_SW_MAX_MIN_MINMAX_ORDERING, Constants.GRAPH_WS_MAX_MIN_MINMAX_ORDERING,

        //ms/dms , max | max
        Constants.GRAPH_SW_MS_MAX_MAX_ORDERING,
        //Constants.GRAPH_WS_MS_MAX_MAX_ORDERING, //included in GRAPH_WS_MAX_MAX_MAX_ORDERING

        Constants.GRAPH_SW_DMS_MAX_MAX_ORDERING,
        //Constants.GRAPH_WS_DMS_MAX_MAX_ORDERING, //included in GRAPH_WS_MIN_MAX_MAXMIN_ORDERING

        //min , ms/dms | min
        //Constants.GRAPH_SW_MIN_MS_MIN_ORDERING, //included in GRAPH_SW_MIN_MAX_MAXMIN_ORDERING
        Constants.GRAPH_WS_MIN_MS_MIN_ORDERING,

        //Constants.GRAPH_SW_MIN_DMS_MIN_ORDERING, //included in GRAPH_SW_MIN_MIN_MIN_ORDERING
        Constants.GRAPH_WS_MIN_DMS_MIN_ORDERING,

        //ms/dms , min | min>=max
        Constants.GRAPH_SW_MS_MIN_MINMAX_ORDERING,
        //Constants.GRAPH_WS_MS_MIN_MINMAX_ORDERING, //included in GRAPH_WS_MAX_MIN_MINMAX_ORDERING

        Constants.GRAPH_SW_DMS_MIN_MINMAX_ORDERING,
        //Constants.GRAPH_WS_DMS_MIN_MINMAX_ORDERING, //included in GRAPH_WS_MIN_MIN_MIN_ORDERING

        //max , ms/dms | min>=max
        //Constants.GRAPH_SW_MAX_MS_MINMAX_ORDERING, //included in GRAPH_SW_MIN_MAX_MAX_ORDERING
        Constants.GRAPH_WS_MAX_MS_MINMAX_ORDERING,

        //Constants.GRAPH_SW_MAX_DMS_MINMAX_ORDERING, //included in GRAPH_SW_MAX_MIN_MINMAX_ORDERING
        Constants.GRAPH_WS_MAX_DMS_MINMAX_ORDERING };

    public static void silenceMode() {
        Config.LOGGER_LEVEL = 0;
        Config.GRAPHICS = false;
    }

    public static boolean isLogDebug() {
        return Config.PRINT_LOG && Config.LOGGER_LEVEL >= 3;
    }
    
    public static boolean isLogOutput() {
        return Config.PRINT_LOG && Config.LOGGER_LEVEL >= 2;
    }

    public static boolean isLogReport() {
        return Config.PRINT_LOG && Config.LOGGER_LEVEL >= 1;
    }
}
