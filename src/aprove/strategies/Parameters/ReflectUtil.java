package aprove.strategies.Parameters;

import java.lang.reflect.*;

import aprove.strategies.Util.*;


public class ReflectUtil {

    public static Field findField(Class<?> targetClass, String value) {
        for (Field f: targetClass.getFields()) { // Check all public static fields
            if (Modifier.isStatic(f.getModifiers()) &&
                    f.getName().equalsIgnoreCase(value)) {
                return f;
            }
        }
        return null; // No such field
    }

    public static Object readField(Field f) throws UnexpectedParamMgrException {
        try {
            return f.get(null);
        } catch (IllegalArgumentException e) {
            throw new UnexpectedParamMgrException(e);
        } catch (IllegalAccessException e) {
            throw new UnexpectedParamMgrException(e);
        }
    }

    public static Method getValueOf_Method(Class<?> parameterClass) {
        try {
            return parameterClass.getMethod("valueOf", String.class);
        } catch (NoSuchMethodException e) {
            return null;
        }
    }

    public static Object callStaticMethod(Method m, String value)
            throws UnexpectedParamMgrException {
        try {
            return m.invoke(null, value);
        } catch (InvocationTargetException e) {
            throw new UnexpectedParamMgrException(e);
        } catch (IllegalArgumentException e) {
            throw new UnexpectedParamMgrException(e);
        } catch (IllegalAccessException e) {
            throw new UnexpectedParamMgrException(e);
        }
    }

    @SuppressWarnings("unchecked")
    public static Enum retrieveEnum(Class argumentClass, String value) throws UserErrorException {
        try {
            return Enum.valueOf(argumentClass, value);
        } catch (IllegalArgumentException e) {
            throw new UserErrorException("\""+value+"\" is not a valid enum constant for "+argumentClass.getName());
        }
    }

    /**
     *
     * @param primitive type name
     * @param value as a String to be parsed by a matching class (e.g. int -> Integer)
     * @return parsed object which will be used as a parameter to invoke a set method
     */
    public static Object convertToPrimitiveType(Class<?> primitive, String value)
            throws UserErrorException {
        try {
        if (Integer.TYPE.equals(primitive)) {
            return Integer.valueOf(value);
        } else if (Boolean.TYPE.equals(primitive)) {
            return Boolean.valueOf(value);
        }
        } catch (NumberFormatException badNumber) {
            throw new UserErrorException(String.format("Expected a %s but got '%s'!",
                    primitive, value));
        }
        throw new UserErrorException("Please implement convert method for primitive data type "+primitive+"!");
    }

}
