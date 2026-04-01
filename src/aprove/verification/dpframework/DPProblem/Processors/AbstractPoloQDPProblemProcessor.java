package aprove.verification.dpframework.DPProblem.Processors;

import aprove.solver.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;

/**
 * Common superclass for all QDP processors which use a polynomial ordering.
 * Used for keeping ranges, degrees, the solver, the factory ...
 *
 * Subclasses should use @ParamsViaArgumentObjects and extend the subclass
 * Arguments.
 *
 * @author Carsten Fuhs
 */
public abstract class AbstractPoloQDPProblemProcessor extends QDPProblemProcessor {

    protected POLOFactory factory;

    protected AbstractPoloQDPProblemProcessor(Arguments arguments) {
        POLOFactory.Arguments facArgs = new POLOFactory.Arguments();
        facArgs.degree = arguments.degree;
        facArgs.range = arguments.range;
        facArgs.maxSimpleDegree = arguments.maxSimpleDegree;
        facArgs.engine = arguments.engine;
        facArgs.satConverter = arguments.satConverter;
        facArgs.simplification = arguments.simplification;
        facArgs.simplifyAll = arguments.simplifyAll;
        facArgs.stripExponents = arguments.stripExponents;
        this.factory = new POLOFactory(facArgs);

    }

    protected static class Arguments {
        public int degree;
        public Engine engine;
        public int maxSimpleDegree;
        public int range;
        public DiophantineSATConverter satConverter;
        public SimplificationMode simplification;
        public boolean simplifyAll;
        public boolean stripExponents;
    }
}
