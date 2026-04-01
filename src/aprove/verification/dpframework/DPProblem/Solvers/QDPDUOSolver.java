package aprove.verification.dpframework.DPProblem.Solvers;

import java.util.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;

public class QDPDUOSolver implements QActiveSolver {

    private SolverFactory solver1;
    private SolverFactory solver2;

    public QDPDUOSolver(DUOFactory factory, SolverFactory order1, SolverFactory order2, SatEngine satEngine) {
        this.solver1 = order1;
        this.solver2 = order2;
    }

    @Override
    public QActiveOrder solveQActive(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R, boolean active, boolean allstrict, Abortion aborter) throws AbortionException {
        // TODO Auto-generated method stub
        return null;
    }

}
