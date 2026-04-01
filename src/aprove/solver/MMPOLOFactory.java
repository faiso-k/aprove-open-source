package aprove.solver;

import java.math.*;
import java.util.logging.*;

import aprove.solver.Engines.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;

/**
 * @author Carsten Fuhs
 * @version $Id$
 */
public class MMPOLOFactory extends SolverFactory {

    private static final Logger log = Logger.getLogger("aprove.solver.MMPOLOFactory");

    private final boolean constAddendInOp;
    private final Heuristic heuristic;
    private final BigInteger range;
    private final DiophantineSATConverter satConverter;
    private final SimplificationMode simplification;
    private final boolean stripExponents;

    public static enum Heuristic {
        ALL_MAX_MIN,
        SUBST,
        GCD,
        DUPL,
        CONS,
        CONSORGCD,
        CAND1,
        CAND1NOMIN,
        CAND2,
        CAND2NOMIN,
        CSIF;
    }

    @ParamsViaArgumentObject
    public MMPOLOFactory(Arguments arguments) {
        super(arguments);
        this.constAddendInOp = arguments.constAddendInOp;
        this.heuristic = arguments.heuristic;
        this.range = BigInteger.valueOf(arguments.range);
        this.satConverter = arguments.satConverter;
        this.simplification = arguments.simplification;
        this.stripExponents = arguments.stripExponents;
    }

    @Override
    public QActiveSolver getQActiveSolver() {
        Engine engine = this.checkEngine(this.getEngine());
        if (MMPOLOFactory.log.isLoggable(Level.INFO)) {
            MMPOLOFactory.log.info("ENGINE: " + engine + "\n");
        }

        MMInterHeuristic interHeuristics = this.getMMHeuristic();
        return new QDPMaxMinPoloSolver(this.range,
                    engine, this.satConverter, interHeuristics,
                    this.simplification, this.stripExponents, this.constAddendInOp);
    }

    private Engine checkEngine(Engine engine) {
        if (engine == null || !(engine instanceof SatEngine || engine instanceof PBSEARCHEngine)) {
            engine = new SAT4JEngine(new SAT4JEngine.Arguments());
        }
        return engine;
    }

    private MMInterHeuristic getMMHeuristic() {
        switch (this.heuristic) {
        case ALL_MAX_MIN: return new FullMMInterHeuristic();
        case SUBST: return new SubstMMInterHeuristic();
        case GCD: return new GcdMMInterHeuristic();
        case DUPL: return new DuplMMInterHeuristic();
        case CONS: return new ConsMMInterHeuristic();
        case CONSORGCD: return new ConsOrGcdMMInterHeuristic();
        case CSIF: return new IfMMInterHeuristic();
        case CAND1: return new Cand1MMInterHeuristic();
        case CAND1NOMIN: return new Cand1NoMinMMInterHeuristic();
        case CAND2: //return new Cand2MMInterHeuristic();
        case CAND2NOMIN: //return new Cand2NoMinMMInterHeuristic();
        default: throw new RuntimeException("Heuristic " + this.heuristic +
                " not integrated yet.");
        }
    }

    public static class Arguments extends SolverFactory.Arguments {
        public boolean constAddendInOp;
        public Heuristic heuristic;
        public int range;
        public DiophantineSATConverter satConverter;
        public SimplificationMode simplification;
        public boolean stripExponents;
    }
    
    @Override
    public boolean deliversCPForders() {
        return false;
    }

}
