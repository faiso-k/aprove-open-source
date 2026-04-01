package aprove.strategies.InstantiationUtils;

import java.lang.reflect.*;
import java.util.*;

import aprove.runtime.*;
import aprove.strategies.Util.*;

/**
 * Creates an instance by invoking the given constructor with all parameters.
 *
 * @see aprove.strategies.Annotations.ParamsViaArguments
 *
 * @author bearperson
 * @version $Id$
 */
public class CreatorViaArguments implements ParametrizedCreator {
    private final Constructor<?> constructor;
    private final Object[] arguments;
    private final boolean[] argsBeenSet;
    private final Class<?>[] paramTypes;
    private final Map<String, Integer> paramNameToIndex;

    public CreatorViaArguments(Constructor<?> constructor, String[] argumentNames) throws ParameterManagerException {
        this.constructor = constructor;
        this.arguments = new Object[argumentNames.length];
        this.argsBeenSet = new boolean[argumentNames.length]; // filled with false by default
        this.paramTypes = constructor.getParameterTypes();

        if (this.paramTypes.length != this.arguments.length) {
            String message = String.format("Number of parameters (%d) declared for" +
                    "class %s differs from the number of constructor arguments (%d).",
                    this.arguments.length, constructor.getDeclaringClass(), this.paramTypes.length);
            throw new UserErrorException(message);
        }

        this.paramNameToIndex = new LinkedHashMap<String, Integer>();
        int i = 0;
        for(String name: argumentNames) {
            this.paramNameToIndex.put(name.toLowerCase(), i++);
        }
    }

    @Override
    public Class<?> getParameterClass(String name) throws ParameterManagerException {
        return this.paramTypes[this.getIndexFor(name)];
    }

    @Override
    public void setParameter(String name, Object value) throws ParameterManagerException {
        int index = this.getIndexFor(name);
        this.arguments[index] = value;
        this.argsBeenSet[index] = true;
    }

    private int getIndexFor(String name) throws ParameterManagerException {
        Integer result = this.paramNameToIndex.get(name.toLowerCase());
        if (result == null) {
            String message = String.format("Unknown parameter '%s' for class '%s', " +
                    "known formats are: %s",
                    name, this.constructor.getDeclaringClass().getName(), this.paramNameToIndex.keySet());
            throw new UserErrorException(message);
        }
        return result;
    }

    @Override
    public Object getInstance() throws ParameterManagerException {
        this.verifyAllArgsSet();
        try {
            return this.constructor.newInstance(this.arguments);
        } catch (IllegalArgumentException e) {
            throw new UserErrorException("Illegal arguments: expected " +
                    this.expectedTypesString() + " but got " + this.providedTypesString());
        } catch (InstantiationException e) {
            throw new UnexpectedParamMgrException(e);
        } catch (IllegalAccessException e) {
            throw new UnexpectedParamMgrException(e);
        } catch (InvocationTargetException e) {
            throw new UnexpectedParamMgrException(e);
        }
    }

    private String expectedTypesString() {
        StringBuffer buf = new StringBuffer();
        boolean mid=false;
        buf.append("[");
        for(Class<?> expected: this.paramTypes) {
            if (mid) {
                buf.append(", ");
            }
            mid=true;
            buf.append(expected.getSimpleName());
        }
        buf.append("]");
        return buf.toString();
    }

    private String providedTypesString() {
        StringBuffer buf = new StringBuffer();
        boolean mid=false;
        buf.append("[");
        int i=0;
        for(String name: this.paramNameToIndex.keySet()) {
            if (mid) {
                buf.append(", ");
            }
            mid=true;
            buf.append(name);
            buf.append(": ");
            if (this.arguments[i] == null) {
                buf.append("null");
            } else {
                buf.append(this.arguments[i].getClass().getSimpleName());
            }
        }
        buf.append("]");
        return buf.toString();
    }

    private void verifyAllArgsSet() throws ParameterManagerException {
        if (! Options.performEagerChecking) {
            return;
        }
        int i=0;
        for(String name: this.paramNameToIndex.keySet()) {
            if (! this.argsBeenSet[i++]) {
                throw new UserErrorException("Required argument '" + name + "' did not get set");
            }
        }
    }

}
