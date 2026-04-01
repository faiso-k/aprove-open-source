package aprove.verification.oldframework.SMT.Solver;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.SMT.*;
import immutables.*;

/**
 * Can be instantiated and parameterized from the strategy.
 */
public interface SMTSolverFactory extends Immutable {

    public SMTSolver getSMTSolver(SMTLIBLogic logic, Abortion abortion);

    public SMTSolver getSMTSolver(SMTLIBLogic logic, Abortion abortion, boolean enable_unsat_core);

}
