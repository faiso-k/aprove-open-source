package aprove.verification.oldframework.SMT.Solver.Factories;

import java.io.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.*;

public class SMTInterpolExtSolverFactory implements SMTSolverFactory {

    @Override
    public SMTSolver getSMTSolver(SMTLIBLogic logic, Abortion abortion, boolean enable_unsat_core) {
        try {
            SExpProcessCommunicator proc =
                new SExpProcessCommunicator(
                    abortion,
                    "java",
                    "-jar",
                    "/local/smtinterpol/smtinterpol.jar"
                );
            return new SMTLIBSolver(logic, proc, enable_unsat_core);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public SMTSolver getSMTSolver(SMTLIBLogic logic, Abortion abortion) {
        return this.getSMTSolver(logic, abortion, false);
    }

}
