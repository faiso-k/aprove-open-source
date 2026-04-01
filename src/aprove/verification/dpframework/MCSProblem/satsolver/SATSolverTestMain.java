package aprove.verification.dpframework.MCSProblem.satsolver;

public class SATSolverTestMain {

    private static final String MINISAT_MODE = "mini";
    private static final String SATCOMP_MODE = "comp";

    private static final int MAX_VAR_PER_LINE = 10;

    public static void main(String[] args) {
        if (args.length < 3) {
            System.err.println("Usage: java SATSolverTestMain <dimacs_file> (comp|mini) <sat_solver_name> [<args>*]");
            System.err.println("  <dimacs_file> must contain a CNF in Dimacs format.");
            System.err.println("  ("+SATSolverTestMain.SATCOMP_MODE+"|"+SATSolverTestMain.MINISAT_MODE+"): 'comp' means that SAT competition style I/O is expected");
            System.err.println("               (as implemented by CryptoMiniSAT, MiniSAT 2.2, ...)");
            System.err.println("               'mini' means that MiniSAT 2.0 style I/O is expected");
            System.err.println("  <sat_solver_name> is the name of the executable to be used as SAT solving backend");
            System.err.println("  <args>       optional command line arguments for the call to the SAT solver");
            return;
        }
        String dimacsFilename = args[0];
        String mode = args[1];
        String command = args[2];
        String solverArgs = SATSolverTestMain.extractSolverArgs(3, args);
        SATSolver satSolver;
        if (SATSolverTestMain.MINISAT_MODE.equals(mode)) {
            satSolver = new MiniSATFileOutputSolver(command, solverArgs);
        } else if (SATSolverTestMain.SATCOMP_MODE.equals(mode)) {
            satSolver = new SATRaceSolver(command, solverArgs);
        } else {
            System.err.println("Second argument must be one of ("+SATSolverTestMain.SATCOMP_MODE+"|"+SATSolverTestMain.MINISAT_MODE+")!");
            return;
        }
        int[] model;
        try {
            model = satSolver.solveFile(dimacsFilename);
        }
        catch (SATSolverException e) {
            System.err.print("An exception occurred during SAT solving:");
            System.err.print(e);
            return;
        }
        SATSolverTestMain.printModel(model);
    }

    private static String extractSolverArgs(int startIndex, String[] args) {
        StringBuilder result = new StringBuilder();
        boolean first = true;
        for (int i = startIndex; i < args.length; i++) {
            if (first) {
                first = false;
            } else {
                result.append(' ');
            }
            result.append(args[i]);
        }
        return result.toString();
    }

    private static void printModel(int[] model) {
        if (model == null) {
            System.out.println("The SAT solver has found the CNF to be unsatisfiable.");
            return;
        }
        System.out.println("The SAT solver has found the following model for the CNF:");
        for (int i = 0; i < model.length; i++) {
            System.out.print(model[i]);
            if ((i+1) % SATSolverTestMain.MAX_VAR_PER_LINE == 0) {
                System.out.println();
            } else {
                System.out.print(' ');
            }
        }
    }
}
