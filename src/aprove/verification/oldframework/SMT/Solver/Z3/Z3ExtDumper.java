package aprove.verification.oldframework.SMT.Solver.Z3;

import java.io.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp.*;

/**
 * Turns a Z3ExtSolverr into a dumper of the SMT queries.
 * @author cryingshadow
 * @version $Id$
 */
public class Z3ExtDumper extends Z3ExtSolver {

    /**
     * @param logic The used logic.
     * @param proc The dumping communicator.
     */
    public Z3ExtDumper(SMTLIBLogic logic, SExpDumpCommunicator proc) {
        super(logic, proc, false);
    }

    /**
     * Dumps the check-sat command.
     * @throws AbortionException Not really thrown.
     * @throws IOException If some I/O error occurs.
     * @throws ParserException Not really thrown.
     */
    public void sendSAT() throws AbortionException, IOException, ParserException {
        this.proc.command(SMTLIBSolver.CheckSat);
    }

}
