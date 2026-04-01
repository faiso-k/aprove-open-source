package aprove.strategies.Parameters;

import aprove.solver.*;
import aprove.strategies.Util.*;
import aprove.verification.dpframework.*;

/**
 * Created on 21.01.2005 by marmer
 *
 * @author: Martin Mertens
 * @version $Id$
 */

public class ParameterManager {

    private ParameterManager() {
    }

    /**
     * Returns a solver with the given NAME, as you would get from
     *
     *  MyProcessor[Engine = NAME]
     */
    public static SolverFactory getSolverFactory(String name) {
        try {
            FuncValue value = new FuncValue(name, FrozenParameters.EMPTY);
            return (SolverFactory) value.get(StrategyTranslator.standardProgram());
        } catch (ParameterManagerException e) {
            throw new ParameterManagerRuntimeException(e);
        }
    }

    /**
     * Given a processor instance, should retrieve the name for that processor in strategy
     */
    public static String getShort(Processor processor) {
        // TODO - Annotation, maybe? Or really read from strategy program, if we have to...
        return processor.getClass().getSimpleName();
    }

    /**
     * Used to wrap away checked exceptions when callers should not be bothered
     * to have to catch them. Used for processors.
     *
     * This construct MUST NOT be used inside stuff called from strategy execution
     * and other Machine thread responsibilities.
     */
    public static class ParameterManagerRuntimeException extends
            RuntimeException {
        private static final long serialVersionUID = 1L;

        public ParameterManagerRuntimeException(Throwable cause) {
            super(cause);
        }
    }
}
