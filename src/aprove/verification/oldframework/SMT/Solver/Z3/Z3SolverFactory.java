package aprove.verification.oldframework.SMT.Solver.Z3;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Solver.*;

public interface Z3SolverFactory extends SMTSolverFactory {

    @Override
    public Z3Solver getSMTSolver(SMTLIBLogic logic, Abortion abortion);

    public Z3Solver getSMTSolver(SMTLIBLogic logic, int timeout, Abortion abortion);

}
