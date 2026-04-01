package aprove.solver;

import java.util.logging.*;

import aprove.solver.Engines.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * @author Carsten Fuhs
 */
public class SCNPFactory extends SolverFactory {

    private static final Logger log = Logger.getLogger("aprove.solver.SCNPFactory");

    // factory for the order used for the argument terms of DPs
    private final SolverFactory order;

    // which multiset comparisons should we try on top of the
    // found level mapping?
    private final boolean max;
    private final boolean min;
    private final boolean ms;
    private final boolean dms;

    // plain level mappings only? (i.e., numeric component becomes 0)
    private final boolean plain;
    // plain-rooted level mappings only? (i.e., numeric component becomes 0)
    private final boolean plainRoot;
    // whole tuple term as additonal argument?
    private final boolean rootArg;
    // handle list of regular arguments
    private final boolean listArgs;


    @ParamsViaArgumentObject
    public SCNPFactory(Arguments arguments) {
        super(arguments);
        this.order = arguments.order;
        this.max = arguments.max;
        this.min = arguments.min;
        this.ms = arguments.ms;
        this.dms = arguments.dms;
        this.plain = arguments.plain;
        this.plainRoot = arguments.plainRoot;
        this.rootArg = arguments.rootArg;
        this.listArgs = arguments.listArgs;
    }

    @Override
    public QActiveSolver getQActiveSolver() {
        SatEngine satEngine = this.checkEngine(this.getEngine());
        if (SCNPFactory.log.isLoggable(Level.INFO)) {
            SCNPFactory.log.info("ENGINE: " + satEngine + "\n");
        }

        return new QDPSCNPSolver(this, this.order, satEngine,
                this.max, this.min, this.ms, this.dms, this.plain, this.plainRoot, this.rootArg, this.listArgs);
    }

    @Override
    public SCNPOrderEncoder getSCNPOrderEncoder(FormulaFactory<None> formulaFactory) {
        throw new UnsupportedOperationException("SCNP atop of SCNP is not supported.");
    }

    private SatEngine checkEngine(Engine engine) {
        if (!(engine instanceof SatEngine)) {
            engine = new SAT4JEngine(new SAT4JEngine.Arguments());
        }
        return (SatEngine) engine;
    }

    public static class Arguments extends SolverFactory.Arguments {

        public SolverFactory order;

        // which multiset comparisons should we try on top of the
        // found level mapping?
        public boolean max = true;
        public boolean min = true;
        public boolean ms  = true;
        public boolean dms = true;

        // plain level mappings only? (i.e., numeric component becomes 0)
        public boolean plain = false;
        // plain-rooted level mappings only? (i.e., numeric component becomes 0)
        public boolean plainRoot = false;
        // additional argument for whole tuple term?
        public boolean rootArg = false;
        // handle list of regular arguments?
        public boolean listArgs = true;
    }

    @Override
    public boolean deliversCPForders() {        
        return this.order.deliversCPForders();
    }

}
