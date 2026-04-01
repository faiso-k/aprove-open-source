package aprove.verification.oldframework.SMT.Solver.Z3;

import java.util.*;

import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.*;

public interface Z3Solver extends SMTSolver {

    public Optional<Model> getModel();

    /**
     * Drop all assumptions and clean up the state of the solver, s.t. it can be used like a fresh one.
     */
    public void reset();

}
