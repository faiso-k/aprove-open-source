package aprove.verification.dpframework.PiDPProblem.Processors;

import aprove.solver.*;

/**
 * Common superclass for all PiDP processors which use a polynomial ordering.
 * Used for keeping ranges, degrees, the solver, the factory ...
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public abstract class AbstractPoloPiDPProblemProcessor extends PiDPProblemProcessor {

    protected final POLOFactory factory;

    protected AbstractPoloPiDPProblemProcessor(Arguments arguments) {
        POLOFactory.Arguments facArgs = new POLOFactory.Arguments();
        facArgs.degree = arguments.degree;
        facArgs.engine = arguments.engine;
        facArgs.maxSimpleDegree = arguments.maxSimpleDegree;
        facArgs.range = arguments.range;
        this.factory = new POLOFactory (facArgs);
    }

    public static class Arguments {
        public int degree;
        public Engine engine;
        public int maxSimpleDegree;
        public int range;
    }

}
