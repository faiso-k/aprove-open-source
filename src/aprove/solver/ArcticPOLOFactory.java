package aprove.solver;

import java.util.*;
import java.util.logging.*;

import aprove.solver.Engines.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Orders.Solvers.*;

/**
 * Factory for POLO with arctic coefficients
 * @author Andreas Kelle-Emden
 * @version $Id:$
 */
public class ArcticPOLOFactory extends SolverFactory {

    protected final static Logger log = Logger.getLogger("aprove.solver.POFactory");

    @ParamsViaArgumentObject
    public ArcticPOLOFactory(Arguments arguments) {
        super(arguments);
    }

    private SMTEngine checkEngine(Engine engine) {
        if (engine instanceof SMTEngine) {
            return (SMTEngine)engine;
        }
        return new YicesEngine();
    }

    @Override
    public QActiveSolver getQActiveSolver() {
        Engine engine = this.checkEngine(this.getEngine());
        return new QDPArcticPOLOSolver((SMTEngine)engine);
    }

    @Override
    public AbortableConstraintSolver<TRSTerm> getSolver(Collection<aprove.verification.dpframework.Orders.Constraint<TRSTerm>> cons) {
        return new ArcticPOLOSolver(this.checkEngine(this.getEngine()));
    }

    @Override
    public boolean deliversCPForders() {        
        return true;
    }

}
