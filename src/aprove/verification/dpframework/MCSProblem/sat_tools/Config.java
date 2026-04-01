package aprove.verification.dpframework.MCSProblem.sat_tools;

/*
 * Sat solvers parameters and which sat solver to use
 */

public class Config {
    public static final int SAT4J = 1;
    public static final int CryptoMiniSATSolver = 2;
    public static final int MiniSATSolver = 3;

    public static final String CryptoMiniSATSolverExecutable = "C:\\SatSolvers\\cryptominisat.exe";
    public static final String MiniSATSolverExecutable = "C:\\SatSolvers\\minisat220.exe";

    //which sat solver to udse
    public static final int SAT_SOLVER = Config.SAT4J;

    // if true create and sav e formula in memory, else in file
    public final static boolean USE_CNF_FILE=true;
    // if true, only dimacs format formula is save in memory
    public final static boolean OLD_METHOD=false;
}
