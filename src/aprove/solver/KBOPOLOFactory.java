package aprove.solver;

import java.util.*;

import aprove.solver.Engines.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.dpframework.TRSProblem.Solvers.*;

/**
 * Factory for KBOPOLO
 * @author Andreas Kelle-Emden
 */
public class KBOPOLOFactory extends SolverFactory {

    @ParamsViaArgumentObject
    public KBOPOLOFactory(Arguments arguments) {
        super(arguments);
    }

    private SMTEngine checkEngine(Engine engine) {
        if (engine instanceof SMTEngine) {
            return (SMTEngine)engine;
        }
        return new YicesEngine();
    }

    @Override
    public DirectSolver getDirectSolver() {
        Engine engine = this.checkEngine(this.getEngine());
        return new KBOPOLOGenericSolver((SMTEngine)engine);
    }

    @Override
    public QActiveSolver getQActiveSolver() {
        Engine engine = this.checkEngine(this.getEngine());
        return new KBOPOLOGenericSolver((SMTEngine)engine);
    }

    @Override
    public RRRSolver getRRRSolver() {
        Engine engine = this.checkEngine(this.getEngine());
        return new KBOPOLOGenericSolver((SMTEngine)engine);
    }

    @Override
    public RRRMuSolver getRRRMuSolver() {
        Engine engine = this.checkEngine(this.getEngine());
        return new KBOPOLOGenericSolver((SMTEngine)engine);
    }

    @Override
    public AbortableConstraintSolver<TRSTerm> getSolver(Collection<aprove.verification.dpframework.Orders.Constraint<TRSTerm>> cons) {
        return new KBOPOLOSolver(this.checkEngine(this.getEngine()));
    }
    
    @Override
    public boolean deliversCPForders() {
        return true;
    }


}
