package aprove.strategies.InstantiationUtils;

import java.lang.reflect.*;
import java.util.*;

import aprove.strategies.Util.*;

/**
 * Provides and caches {@link Setter} objects for classes.
 *
 * @author bearperson
 * @version $Id$
 */
class SetterCache {
    public static final String SETTER_PREFIX = "set";

    private static final Map<Class<?>, Map<String, Setter>> methodMap =
            new HashMap<Class<?>, Map<String,Setter>>();
    private static final Map<Class<?>, Map<String, Setter>> fieldAndMethodMap =
        new HashMap<Class<?>, Map<String, Setter>>();

    /**
     * Returns Setter objects for everything that looks like a parameter name.
     *
     * If a set* method is present, it is used,
     * otherwise a public nonstatic field is tried.
     */
    public static synchronized Map<String, Setter> getFieldsAndMethods(Class<?> cl) throws ParameterManagerException {
        Map<String, Setter> result = SetterCache.fieldAndMethodMap.get(cl);

        if (result == null) {
            result = new HashMap<String, Setter>();

            SetterCache.fillFields(cl, result);
            result.putAll(SetterCache.getMethods(cl));
            result = Collections.unmodifiableMap(result);
            SetterCache.fieldAndMethodMap.put(cl, result);
        }
        return result;
    }

    /**
     * Returns Setter objects for everything that looks like a parameter name.
     *
     * Uses only set* methods.
     */
    public static synchronized Map<String, Setter> getMethods(Class<?> cl)
            throws ParameterManagerException {
        Map<String, Setter> result = SetterCache.methodMap.get(cl);

        if (result == null) {
            result = new HashMap<String, Setter>();

            SetterCache.fillMethods(cl, result);
            result = Collections.unmodifiableMap(result);
            SetterCache.methodMap.put(cl, result);

        }
        return result;
    }

    private static void fillFields(Class<?> cl,
            Map<String, Setter> result)
            throws ParameterManagerException {
        for (Field field: cl.getFields()) {
            int modifiers = field.getModifiers();
            if (Modifier.isFinal(modifiers) || Modifier.isStatic(modifiers)) {
                continue;
            }
            String name = field.getName();
            Setter newValue = new FieldSetter(field);
            Setter oldValue = result.put(name.toLowerCase(), newValue);

            if (oldValue != null) {
                throw new UserErrorException("Problem in ParameterManager: "+
                        "Class "+cl+" has two fields with same case-insensitive name "+name+"!");
            }
        }
    }

    private static void fillMethods(Class<?> cl,
            Map<String, Setter> result)
            throws ParameterManagerException {
        for (Method method: cl.getMethods()) {
            String name = method.getName();
            Class<?>[] args = method.getParameterTypes();
            if (name.startsWith(SetterCache.SETTER_PREFIX) && args.length == 1) {
                String rest = name.substring(SetterCache.SETTER_PREFIX.length());
                Setter newValue = new MethodSetter(method);
                Setter oldValue = result.put(rest.toLowerCase(), newValue);

                if (oldValue != null) {
                    throw new UserErrorException("Problem in ParameterManager: "+
                            "Class "+cl+" has two setters with same postfix "+rest+"!");
                }
            }
        }
    }
}
