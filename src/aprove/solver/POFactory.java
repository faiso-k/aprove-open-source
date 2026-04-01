package aprove.solver;

import java.util.*;
import java.util.logging.*;

import aprove.solver.Engines.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Processors.QDPSizeChangeProcessor.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.dpframework.TRSProblem.Solvers.*;

public abstract class POFactory extends SolverFactory {

    protected static final Logger log = Logger.getLogger("aprove.solver.POFactory");

    protected final boolean quasi;
    protected final boolean breadth;
    protected final int restriction;
    protected AFSType afsType;

    protected final String name;

    public POFactory(String name, Arguments arguments) {
        super(arguments);
        this.name = name;

        this.afsType = arguments.afsType;
        this.breadth = arguments.breadth;
        this.quasi = arguments.quasi;
        this.restriction = arguments.restriction;
    }

    public static Map<String, Object> getDefaultConfiguration(String name) {
        HashMap<String, Object> dconf = new HashMap<String, Object>();
        dconf.put("breadth", POFactory.getDefaultBreadth(name));
        dconf.put("quasi", POFactory.getDefaultQuasi(name));
        dconf.put("restriction", POFactory.getDefaultRestriction(name));
        return dconf;
    }

    /**
     * Check if we can use <code>engine</code> as Engine for the corresponding
     * order. Returns engine if so, otherwise some suitable default engine is
     * returned.
     */
    protected abstract Engine checkEngine(Engine engine);

    @Override
    public QActiveSolver getQActiveSolver() {
        Engine engine = this.checkEngine(this.getEngine());
        java.util.logging.Logger.getLogger("").info("ENGINE: "+engine);
        if (engine instanceof YNMPEVLEngine) {
            return new QDPAfsOrderSolver(this, this.restriction);
        }
        return new QDPSATPOSolver(this);
    }

    @Override
    public DirectSolver getDirectSolver() {
        Engine engine = this.checkEngine(this.getEngine());
        java.util.logging.Logger.getLogger("").info("ENGINE: "+engine);
        // if afsType is set to FULLAFS, it is not possible to use a direct solver!
        if (this.afsType == AFSType.FULLAFS) {
            POFactory.log.log(Level.FINE, "Full argument filtering is not allowed with direct termination proofs!\n");
            POFactory.log.log(Level.FINE, "Switching to no argument filtering.\n");
            this.afsType = AFSType.NOAFS;
        }
        if (engine instanceof YNMPEVLEngine) {
            return new AbortableDirectSolver(this);
        }
        return new SATDirectSolver(this);
    }

    @Override
    public RRRSolver getRRRSolver() {
        Engine engine = this.checkEngine(this.getEngine());
        java.util.logging.Logger.getLogger("").info("ENGINE: "+engine);
        // if afsType is set to FULLAFS, it is not possible to use a direct solver!
        if (this.afsType == AFSType.FULLAFS) {
            POFactory.log.log(Level.FINE, "Full argument filtering is not allowed with RRR termination proofs!\n");
            POFactory.log.log(Level.FINE, "Switching to no argument filtering.\n");
            this.afsType = AFSType.NOAFS;
        }
        if (engine instanceof YNMPEVLEngine) {
            return new AbortableRRRSolver(this);
        }
        return new SATRRRSolver(this);
    }

    @Override
    public RRRMuSolver getRRRMuSolver() {
        Engine engine = this.checkEngine(this.getEngine());
        java.util.logging.Logger.getLogger("").info("ENGINE: "+engine);
        // if afsType is set to FULLAFS, it is not possible to use a direct solver!
        if (this.afsType == AFSType.FULLAFS) {
            POFactory.log.log(Level.FINE, "Full argument filtering is not allowed with RRR termination proofs!\n");
            POFactory.log.log(Level.FINE, "Switching to no argument filtering.\n");
            this.afsType = AFSType.NOAFS;
        }
        if (engine instanceof YNMPEVLEngine) {
            throw new UnsupportedOperationException("Mu-monotonicity is not supported by non-SAT solvers, yet.");
        }
        return new SATRRRMuSolver(this);
    }

    @Override
    public RuleChecker getRuleChecker() {
        Engine engine = this.checkEngine(this.getEngine());
        if (!(engine instanceof SatEngine)) {
            throw new UnsupportedOperationException("getRuleChecker not implemented for " + engine.getClass());
        }
        return new SATPORuleChecker(this);
    }

    protected static boolean getDefaultBreadth(String name) {
        return Boolean.valueOf(MetaSolverFactory.getDefault(name+".breadth"));
    }

    protected static boolean getDefaultQuasi(String name) {
        return Boolean.valueOf(MetaSolverFactory.getDefault(name+".quasi"));
    }

    protected static int getDefaultRestriction(String name) {
        return Integer.valueOf(MetaSolverFactory.getDefault(name+".restriction"));
    }

    public static class Arguments extends SolverFactory.Arguments {
        public AFSType afsType = AFSType.FULLAFS;
        public boolean breadth;
        public boolean quasi;
        public int restriction;
    }

}
