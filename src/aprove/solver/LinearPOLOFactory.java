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

/**
 * Factory for linear POLO
 * @author Andreas Kelle-Emden
 */
public class LinearPOLOFactory extends SolverFactory {

    protected final static Logger log = Logger.getLogger("aprove.solver.POFactory");

    protected AFSType afsType;
    protected final int numBits;

    @ParamsViaArgumentObject
    public LinearPOLOFactory(Arguments arguments) {
        super(arguments);
        this.afsType = arguments.afsType;
        this.numBits = arguments.numBits;
    }

    private SMTEngine checkEngine(Engine engine) {
        if (engine instanceof SMTEngine) {
            return (SMTEngine)engine;
        }
        return new YicesEngine();
    }

    @Override
    public DirectSolver getDirectSolver() {
        if (this.afsType == AFSType.FULLAFS) {
            LinearPOLOFactory.log.log(Level.FINE, "Full argument filtering is not allowed with direct termination proofs!\n");
            LinearPOLOFactory.log.log(Level.FINE, "Switching to monotone argument filtering.\n");
            this.afsType = AFSType.MONOTONEAFS;
        }
        Engine engine = this.checkEngine(this.getEngine());
        return new LinearPOLODirectSolver((SMTEngine)engine, this.afsType, this.numBits);
    }

    @Override
    public QActiveSolver getQActiveSolver() {
        Engine engine = this.checkEngine(this.getEngine());
        return new QDPLinearPOLOSolver((SMTEngine)engine, this.afsType, this.numBits);
    }

    @Override
    public RRRSolver getRRRSolver() {
        if (this.afsType == AFSType.FULLAFS) {
            LinearPOLOFactory.log.log(Level.FINE, "Full argument filtering is not allowed with RRR termination proofs!\n");
            LinearPOLOFactory.log.log(Level.FINE, "Switching to monotone argument filtering.\n");
            this.afsType = AFSType.MONOTONEAFS;
        }
        Engine engine = this.checkEngine(this.getEngine());
        return new LinearPOLORRRSolver((SMTEngine)engine, this.afsType, this.numBits);
    }

    @Override
    public RRRMuSolver getRRRMuSolver() {
        if (this.afsType == AFSType.FULLAFS) {
            LinearPOLOFactory.log.log(Level.FINE, "Full argument filtering is not allowed with RRR termination proofs!\n");
            LinearPOLOFactory.log.log(Level.FINE, "Switching to monotone argument filtering.\n");
            this.afsType = AFSType.MONOTONEAFS;
        }
        Engine engine = this.checkEngine(this.getEngine());
        return new LinearPOLORRRSolver((SMTEngine)engine, this.afsType, this.numBits);
    }

    @Override
    public AbortableConstraintSolver<TRSTerm> getSolver(Collection<aprove.verification.dpframework.Orders.Constraint<TRSTerm>> cons) {
        return new LinearPOLOSolver(this.checkEngine(this.getEngine()), this.afsType, this.numBits);
    }

    public static class Arguments extends SolverFactory.Arguments {
        public AFSType afsType = AFSType.NOAFS;
        public int numBits = 0;
    }
    
    @Override
    public boolean deliversCPForders() {
        return true;
    }

}
