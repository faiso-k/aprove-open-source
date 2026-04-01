package aprove.solver;

import java.math.*;
import java.util.logging.*;

import aprove.solver.Engines.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;

/**
 * @author Carsten Fuhs
 * @version $Id$
 */
public class NEGPOLOFactory extends SolverFactory {

    public enum NegRangeCriterion {
        // try negative constants for each and every symbol
        ALWAYS,

        // try negative constants only for symbols of arity > 0
        NON_CONSTANTS,

        // try negative symbols only for symbols
        // that occur above another symbol on a RHS
        DAMPEN;
    }

    private static final Logger log = Logger.getLogger("aprove.solver.NEGPOLOFactory");

    private final BigInteger posConstantRange;
    private final BigInteger negConstantRange;
    private final BigInteger range;
    private final int restriction;
    private final DiophantineSATConverter satConverter;
    private final NegRangeCriterion negRangeCriterion;
    private final boolean partialDioEval;

    @ParamsViaArgumentObject
    public NEGPOLOFactory(Arguments arguments) {
        super(arguments);
        this.negConstantRange = BigInteger.valueOf(arguments.negConstantRange);
        this.posConstantRange = BigInteger.valueOf(arguments.posConstantRange);
        this.range = BigInteger.valueOf(arguments.range);
        this.restriction = arguments.restriction;
        this.satConverter = arguments.satConverter;
        this.negRangeCriterion = arguments.negRangeCriterion;
        this.partialDioEval = arguments.partialDioEval;
    }

    @Override
    public QActiveSolver getQActiveSolver() {
        Engine engine = this.checkEngine(this.getEngine());
        if (NEGPOLOFactory.log.isLoggable(Level.INFO)) {
            NEGPOLOFactory.log.info("ENGINE: " + engine + "\n");
        }

        if (engine instanceof DYNAMICNEGPOLOEngine) {
            return new QDPNegPoloSolver(this.range, this.restriction, engine);
        }
        else {
            // if the following cast does not work, probably a new engine
            // for NEGPOLO needs to be integrated here
            SatEngine satEngine = (SatEngine) engine;

            return new QDPNegPoloSolver(this.range, this.posConstantRange,
                    this.negConstantRange, satEngine, this.satConverter,
                    this.negRangeCriterion, this.partialDioEval);
        }
    }

    private Engine checkEngine(Engine engine) {
        if (engine == null || !(engine instanceof SatEngine ||
                engine instanceof DYNAMICNEGPOLOEngine)) {
            engine = new SAT4JEngine(new SAT4JEngine.Arguments());
        }
        return engine;
    }

    public static class Arguments extends SolverFactory.Arguments {
        public NegRangeCriterion negRangeCriterion;
        public int posConstantRange;
        public int negConstantRange;
        public int range;
        public int restriction;
        public DiophantineSATConverter satConverter;
        public boolean partialDioEval;
    }

    @Override
    public boolean deliversCPForders() {
        return true;
    }

}
