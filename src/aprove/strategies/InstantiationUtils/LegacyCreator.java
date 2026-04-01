package aprove.strategies.InstantiationUtils;

import aprove.strategies.Util.*;

/**
 * Instantiates a given class, then invokes setters on it to set parameters.
 *
 * @see aprove.strategies.Annotations.ParamsViaSetterMethods
 *
 * @author bearperson
 * @version $Id$
 */
public class LegacyCreator implements ParametrizedCreator {
    private final ParameterSettingHelper backend;

    public LegacyCreator(Class<?> targetClass) throws ParameterManagerException {
        this.backend = ParameterSettingHelper.createWithoutFields(targetClass);
    }

    @Override
    public Class<?> getParameterClass(String name) throws ParameterManagerException {
        return this.backend.getParameterClass(name);
    }

    @Override
    public void setParameter(String name, Object value) throws ParameterManagerException {
        Class<?> targetClass = this.backend.getTargetClass();
        this.backend.setParameter(name, value);
    }

    @Override
    public Object getInstance() throws UnexpectedParamMgrException {
        return this.backend.getInstance();
    }

}
