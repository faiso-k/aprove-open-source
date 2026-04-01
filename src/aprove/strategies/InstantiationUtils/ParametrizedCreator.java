package aprove.strategies.InstantiationUtils;

import aprove.strategies.Util.*;

/**
 * Wrapper that creates a Processor/Solver with a bunch of parameters.
 *
 * Implementors may choose to collect all parameters, using them when
 * getInstance() is called, or set them as they go along.
 *
 * @author bearperson
 * @version $Id$
 */
public interface ParametrizedCreator {

    /**
     * Returns the class we expect a given parameter to have.
     * This is used in the ParameterManager for some heuristics.
     */
    Class<?> getParameterClass(String name) throws ParameterManagerException;

    void setParameter(String name, Object value) throws ParameterManagerException;

    /**
     * Returns an instance of the to-be-instantiated class with all parameters set.
     */
    Object getInstance() throws ParameterManagerException;
}
