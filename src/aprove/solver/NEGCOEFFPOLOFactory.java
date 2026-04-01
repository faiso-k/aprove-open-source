package aprove.solver;

import java.math.*;
import java.util.logging.*;

import aprove.solver.Engines.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;

/**
 * @author Carsten Fuhs
 * @version $Id$
 */
public class NEGCOEFFPOLOFactory extends NegOpPOLOFactory {

    private static final Logger log = Logger.getLogger("aprove.solver.NEGCOEFFPOLOFactory");

    private final BigInteger negRange;
    private final BigInteger posRange;
    private final DiophantineSATConverter satConverter;
    private final SimplificationMode simplification;
    private final boolean stripExponents;

    @ParamsViaArgumentObject
    public NEGCOEFFPOLOFactory(Arguments arguments) {
        super(arguments);

        this.negRange = BigInteger.valueOf(arguments.negRange);
        this.posRange = BigInteger.valueOf(arguments.posRange);
        this.satConverter = arguments.satConverter;
        this.simplification = arguments.simplification;
        this.stripExponents = arguments.stripExponents;
    }

    @Override
    public boolean solversGenerateCECompatibleOrders() {
        // Prevoiusly, it said "false" because of (=, >)
        // as reduction pair, but in case you use (>=, >)
        // as reduction pair (as usual), "true" is the
        // correct answer. (Likewise, many other orders
        // would become non-CE-compatible if you used
        // (=, >) as reduction pair.)
        return true;
    }

    @Override
    public QActiveSolver getQActiveSolver() {
        Engine engine = this.checkEngine(this.getEngine());
        if (NEGCOEFFPOLOFactory.log.isLoggable(Level.INFO)) {
            NEGCOEFFPOLOFactory.log.info("ENGINE: " + engine + "\n");
        }

        NCInterHeuristic interHeuristics = this.getNCHeuristic();
        return new QDPNegCoeffPoloSolver(this.posRange, this.negRange,
                    engine, this.satConverter, interHeuristics,
                    this.simplification, this.stripExponents);
    }

    private Engine checkEngine(Engine engine) {
        if (engine == null || !(engine instanceof SatEngine || engine instanceof PBSEARCHEngine)) {
            engine = new SAT4JEngine(new SAT4JEngine.Arguments());
        }
        return engine;
    }

    public static class Arguments extends NegOpPOLOFactory.Arguments {
        public int negRange;
        public int posRange;
        public DiophantineSATConverter satConverter;
        public SimplificationMode simplification;
        public boolean stripExponents;
    }
    
    @Override
    public boolean deliversCPForders() {
        return false;
    }


}
