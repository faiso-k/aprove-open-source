package aprove.verification.oldframework.SMT.Solver.Factories;

import java.io.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.SMT.Solver.SMTInterpol.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.*;

/**
 * Calls the SMT solver SMTInterpol within the very same JVM as AProVE.
 * This means only little startup overhead, but it is asymptotically
 * probably not the fastest. Good if your SMT instances are small,
 * but you have many of them. (This is analogous to SAT4J instead of
 * more efficient external solvers like MiniSAT for standard SAT
 * instances.)
 *
 * @author fuhs
 */
public class SMTInterpolIntSolverFactory implements SMTSolverFactory {

    @Override
    public SMTInterpolIntSolver getSMTSolver(SMTLIBLogic logic, Abortion aborter) {
        return new SMTInterpolIntSolver(logic, aborter);
    }

    @Override
    public SMTSolver getSMTSolver(SMTLIBLogic logic, Abortion aborter, boolean enableUnsatCore) {
        try {
            SExpProcessCommunicator proc =
                new SExpProcessCommunicator(
                    aborter,
                    "java",
                    "-jar",
                    "/local/smtinterpol/smtinterpol.jar"
                );
            return new SMTLIBSolver(logic, proc, enableUnsatCore);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

}
