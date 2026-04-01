package aprove.strategies.InstantiationUtils;

import aprove.strategies.Util.*;

/**
 * Wraps a way to set a specific parameter for a fixed class:
 * (e.g. A public nonstatic field or set* method)
 *
 * @author bearperson
 * @version $Id$
 */
interface Setter {
    Class<?> getExpectedType();

    /**
     * @param target Instance to modify
     */
    void set(Object target, Object value) throws ParameterManagerException;
}
