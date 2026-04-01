package aprove.strategies.InstantiationUtils;

import java.util.*;
import java.util.logging.*;

import aprove.strategies.Util.*;

/**
 * Creates an instance of a class and sets parameters via setter methods
 * (or optionally, falling back to using public nonstatic fields)
 * on this instance.
 *
 * @author bearperson
 * @version $Id$
 */
class ParameterSettingHelper {
    private static final Logger log = Logger.getLogger("aprove.Processors.Parameters");

    private final Object target;
    private final Class<?> targetClass;
    private final Map<String, Setter> setters;

    protected ParameterSettingHelper(Class<?> targetClass, Map<String, Setter> setters) throws UnexpectedParamMgrException {
        this.targetClass = targetClass;
        this.setters = setters;
        try {
            this.target = targetClass.newInstance();
        } catch (InstantiationException e) {
            throw new UnexpectedParamMgrException(e);
        } catch (IllegalAccessException e) {
            throw new UnexpectedParamMgrException(e);
        }
    }

    /**
     * Creates an instance which uses only set* methods
     */
    public static ParameterSettingHelper createWithoutFields(Class<?> targetClass) throws ParameterManagerException {
        return new ParameterSettingHelper(targetClass, SetterCache.getMethods(targetClass));
    }

    /**
     * Creates an instance which tries set* methods,
     * falling back to public nonstatic fields if no method of the name is available.
     */
    public static ParameterSettingHelper createWithFields(Class<?> targetClass) throws ParameterManagerException {
        return new ParameterSettingHelper(targetClass, SetterCache.getFieldsAndMethods(targetClass));
    }

    public Class<?> getTargetClass() {
        return this.targetClass;
    }

    /**
     * @see ParametrizedCreator#getParameterClass(String)
     */
    public Class<?> getParameterClass(String name) throws ParameterManagerException {
        return this.getSetter(name).getExpectedType();
    }

    public void setParameter(String name, Object value) throws ParameterManagerException {
        Setter setter = this.getSetter(name);
        if (ParameterSettingHelper.log.isLoggable(Level.FINEST)) {
            String message = String.format("ParameterManager: Setting parameter " +
                    "%s via %s to argument %s of type %s", name, setter,
                    value.toString(), value.getClass().getName());
            ParameterSettingHelper.log.log(Level.FINEST, message);
        }
        setter.set(this.target, value);
    }

    private Setter getSetter(String name) throws ParameterManagerException {
        Setter result = this.setters.get(name.toLowerCase());
        if (result == null) {
            throw new UserErrorException("Class " + this.targetClass.getName()+
                    " must implement a way to set " + name);
        }
        return result;
    }

    public Object getInstance() {
        return this.target;
    }

}
