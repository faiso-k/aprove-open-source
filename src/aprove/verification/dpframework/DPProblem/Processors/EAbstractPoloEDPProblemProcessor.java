package aprove.verification.dpframework.DPProblem.Processors;

import aprove.solver.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;

/**
 * Common superclass for all EDP processors which use a polynomial ordering.
 * Used for keeping ranges, degrees, the solver, the factory ...
 *
 * @author stein
 * @version $Id$
 */
public abstract class EAbstractPoloEDPProblemProcessor extends EDPProblemProcessor {

    protected POLOFactory factory;

    protected EAbstractPoloEDPProblemProcessor(Arguments arguments) {
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

    public static class Arguments {
        public int degree;
        public int range;
        public Engine engine;
        public int maxSimpleDegree;
        public DiophantineSATConverter satConverter;
        public SimplificationMode simplification;
        public boolean simplifyAll;
        public boolean stripExponents;
    }
}
