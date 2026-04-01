package aprove.solver;

import java.util.*;
import java.util.logging.*;

import aprove.solver.Engines.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.dpframework.TRSProblem.Solvers.*;

@SuppressWarnings("serial")
public class KBOFactory extends POFactory {

    private final boolean status;

    @ParamsViaArgumentObject
    public KBOFactory(Arguments arguments) {
        super("KBO", arguments);
        this.status = arguments.status;
    }

    @Override
    public QActiveSolver getQActiveSolver() {
        Engine engine = this.checkEngine(this.getEngine());
        java.util.logging.Logger.getLogger("").info("ENGINE: "+engine);
        if (engine instanceof YNMPEVLEngine) {
            return new QDPAfsOrderSolver(this, this.restriction);
        } else if (engine instanceof SMTEngine) {
            return new QDPKBOSMTSolver(this.quasi, this.status, (SMTEngine)engine);
        } else {
            /* cannot happen, as checkEngine allows only the engines above */
            throw new RuntimeException("Internal error");
        }
    }

    @Override
    public DirectSolver getDirectSolver() {
        Engine engine = this.checkEngine(this.getEngine());
        java.util.logging.Logger.getLogger("").info("ENGINE: "+engine);
        // if afsType is set to FULLAFS, it is not possible to use a direct solver!
        if (this.afsType == AFSType.FULLAFS) {
            POFactory.log.log(Level.FINE, "Full argument filtering is not allowed with direct termination proofs!\n");
            POFactory.log.log(Level.FINE, "Switching to monotone argument filtering.\n");
            this.afsType = AFSType.MONOTONEAFS;
        }
        if (engine instanceof YNMPEVLEngine) {
            return new AbortableDirectSolver(this);
        } else if (engine instanceof SMTEngine) {
            return new SMTKBODirectSolver(this.quasi, this.status, (SMTEngine)engine);
        } else {
            /* cannot happen, as checkEngine allows only the engines above */
            throw new RuntimeException("Internal error");
        }
    }

    @Override
    public RRRSolver getRRRSolver() {
        Engine engine = this.checkEngine(this.getEngine());
        java.util.logging.Logger.getLogger("").info("ENGINE: "+engine);
        // if afsType is set to FULLAFS, it is not possible to use a direct solver!
        if (this.afsType == AFSType.FULLAFS) {
            POFactory.log.log(Level.FINE, "Full argument filtering is not allowed with RRR termination proofs!\n");
            POFactory.log.log(Level.FINE, "Switching to monotone argument filtering.\n");
            this.afsType = AFSType.MONOTONEAFS;
        }
        if (engine instanceof YNMPEVLEngine) {
            return new AbortableRRRSolver(this);
        } else if (engine instanceof SMTEngine) {
            return new SMTKBORRRSolver(this.quasi, this.status, (SMTEngine)engine);
        } else {
            /* cannot happen, as checkEngine allows only the engines above */
            throw new RuntimeException("Internal error");
        }
    }

    @Override
    public AbortableConstraintSolver<TRSTerm> getSolver(Collection<aprove.verification.dpframework.Orders.Constraint<TRSTerm>> cons) {
        Engine engine = this.checkEngine(this.getEngine());
        if (engine instanceof SMTEngine) {
            return new KBOSMTSolver(this.quasi, this.status, (SMTEngine)engine);
        }
        return aprove.verification.dpframework.Orders.Solvers.KBOSolver.create();
    }

    @Override
    protected Engine checkEngine(Engine engine) {
        if (engine instanceof YNMPEVLEngine || engine instanceof SMTEngine) {
                return engine;
            }
        return new YNMPEVLEngine();
    }

    public static class Arguments extends POFactory.Arguments {
        public boolean status;

        {
            this.breadth = POFactory.getDefaultBreadth("KBO");
            this.quasi = POFactory.getDefaultQuasi("KBO");
            this.restriction = POFactory.getDefaultRestriction("KBO");
        }
    }

    @Override
    public boolean deliversCPForders() {        
        return true;
    }
}
