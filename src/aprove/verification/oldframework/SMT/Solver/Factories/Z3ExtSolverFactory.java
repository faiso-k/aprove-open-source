package aprove.verification.oldframework.SMT.Solver.Factories;

import java.io.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.*;
import aprove.verification.oldframework.SMT.Solver.Z3.*;

/**
 * Factory to create extern Z3 solvers.
 * @author unknown, cryingshadow
 * @version $Id$
 */
public class Z3ExtSolverFactory implements Z3SolverFactory {

    /**
     * @param writer A writer to dump SMT queries to.
     * @param logic The used logic for the queries.
     * @param abortion Aborter.
     * @return A query dumper.
     */
    public Z3ExtDumper getDumper(FileWriter writer, SMTLIBLogic logic, Abortion abortion) {
        try {
            return new Z3ExtDumper(logic, new SExpDumpCommunicator(writer, abortion));
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public Z3Solver getSMTSolver(SMTLIBLogic logic, Abortion abortion) {
        return this.getSMTSolver(logic, abortion, false);
    }

    @Override
    public Z3ExtSolver getSMTSolver(SMTLIBLogic logic, Abortion abortion, boolean enable_unsat_core) {
        try {
            SExpProcessCommunicator proc = new SExpProcessCommunicator(abortion, "z3", "-smt2", "-in");
            return new Z3ExtSolver(logic, proc, enable_unsat_core);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public Z3Solver getSMTSolver(final SMTLIBLogic logic, final int timeout, final Abortion abortion) {
        throw new NotYetImplementedException();
    }

}
