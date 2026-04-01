package aprove.solver;

import java.math.*;
import java.util.logging.*;

import aprove.solver.Engines.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.NonMonMaxPolo.*;
import aprove.verification.dpframework.Orders.Utility.NonMonMaxPolo.Heuristics.*;

/**
 * @author Carsten Fuhs
 */
public class NonMonPOLOFactory extends SolverFactory {

    private static final Logger log = Logger.getLogger("aprove.solver.NonMonPOLOFactory");

    private final Heuristic heuristic;
    private final BigInteger negRange;
    private final BigInteger posRange;
    private final DiophantineSATConverter satConverter;

    public static enum Heuristic {
        FULL, DIV, DIVMIN, CAND1, CAND2, CAND3;
    }

    @ParamsViaArgumentObject
    public NonMonPOLOFactory(Arguments arguments) {
        super(arguments);
        this.heuristic = arguments.heuristic;
        this.negRange = BigInteger.valueOf(arguments.negRange);
        this.posRange = BigInteger.valueOf(arguments.posRange);
        this.satConverter = arguments.satConverter;
    }

    @Override
    public boolean solversGenerateCECompatibleOrders() {
        // Previously, it said "false" because of (=, >)
        // as reduction pair, but in case you use (>=, >)
        // as reduction pair (as usual), "true" is the
        // correct answer. (Likewise, many other orders
        // would become non-CE-compatible if you used
        // (=, >) as reduction pair.)
        return true;
    }


    public QDPNonMonPoloSolver getQDPNonMonPoloSolver() {
        Engine engine = this.checkEngine(this.getEngine());
        if (NonMonPOLOFactory.log.isLoggable(Level.INFO)) {
            NonMonPOLOFactory.log.info("ENGINE: " + engine + "\n");
        }

        NonMonInterHeuristic interHeuristics = this.getNonMonHeuristic();

        return new QDPNonMonPoloSolver(this.posRange, this.negRange,
                    engine, this.satConverter, interHeuristics);
    }

    private Engine checkEngine(Engine engine) {
        if (engine == null || !(engine instanceof SatEngine)) {
            engine = new SAT4JEngine(new SAT4JEngine.Arguments());
        }
        return engine;
    }

    private NonMonInterHeuristic getNonMonHeuristic() {
        switch (this.heuristic) {
        case CAND1: return new NonMonCand1Heuristic();
        case CAND2: return new NonMonCand2Heuristic();
        case CAND3: return new NonMonCand3Heuristic();
        case FULL: return new FullHeuristic();
        case DIV: return new DivHeuristic();
        case DIVMIN: //return new DivMinHeuristic();
        default: throw new RuntimeException("Heuristic " + this.heuristic +
                " not integrated yet.");
        }
    }

    public static class Arguments extends SolverFactory.Arguments {
        public Heuristic heuristic;
        public int negRange;
        public int posRange;
        public DiophantineSATConverter satConverter;
    }
    
    @Override
    public boolean deliversCPForders() {
        return false;
    }


}
