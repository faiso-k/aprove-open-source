package aprove.strategies.InstantiationUtils;

import java.lang.reflect.*;

import aprove.strategies.Util.*;

/**
 * Instantiates a given class: First, parameters are collected in an
 * "arguments object", then the constructor of the class is called
 * with that object as sole argument.
 *
 * The reasoning is that this allows the class to be immutable, while still
 * keeping the constructor declaration short and inheritance easy.
 *
 * @see aprove.strategies.Annotations.ParamsViaArgumentObject
 *
 * @author bearperson
 * @version $Id$
 */
public class CreatorViaArgumentObject implements ParametrizedCreator {
    private final Constructor<?> constructor;
    private final ParameterSettingHelper backend;

    public CreatorViaArgumentObject(Constructor<?> constructor, Class<?> argumentClass) throws ParameterManagerException {
        this.constructor = constructor;
        this.backend = ParameterSettingHelper.createWithFields(argumentClass);
    }

    @Override
    public Class<?> getParameterClass(String name) throws ParameterManagerException {
        return this.backend.getParameterClass(name);
    }

    @Override
    public void setParameter(String name, Object value) throws ParameterManagerException {
        this.backend.setParameter(name, value);
    }

    @Override
    public Object getInstance() throws UnexpectedParamMgrException {
        Object setterInstance = this.backend.getInstance();
        try {
            return this.constructor.newInstance(setterInstance);
        } catch (InstantiationException e) {
            throw new UnexpectedParamMgrException(e);
        } catch (IllegalAccessException e) {
            throw new UnexpectedParamMgrException(e);
        } catch (InvocationTargetException e) {
            throw new UnexpectedParamMgrException(e);
        }
    }

}
