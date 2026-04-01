package aprove.verification.oldframework.SMT.Solver.Factories;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Solver.Z3.*;

public class Z3IntSolverFactory implements Z3SolverFactory {

    @Override
    public Z3Solver getSMTSolver(final SMTLIBLogic logic, final int timeout, final Abortion abortion) {
        return new Z3IntSolver(logic, timeout, abortion);
    }

    @Override
    public Z3Solver getSMTSolver(SMTLIBLogic logic, Abortion abortion, boolean enable_unsat_core) {
        if (enable_unsat_core) {
            throw new RuntimeException("Unsat cores yet implemented for Z3IntSolver");
        }
        return new Z3IntSolver(logic, Integer.MAX_VALUE, abortion);
    }

    @Override
    public Z3Solver getSMTSolver(SMTLIBLogic logic, Abortion abortion) {
        return this.getSMTSolver(logic, abortion, false);
    }

}
