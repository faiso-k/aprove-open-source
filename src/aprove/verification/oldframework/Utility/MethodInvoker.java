package aprove.verification.oldframework.Utility;

import java.lang.reflect.*;

/**
 * Functional class to wrap some reflection functionality for invoking methods.
 * Like this, import of libraries is done at runtime, not at compile time.
 * Useful if some libraries are not always included.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public abstract class MethodInvoker {

    private static ClassLoader classLoader = ClassLoader.getSystemClassLoader(); // cache it

    /**
     * Invokes a method of a given Object.
     *
     * @param object  the object whose method is to be invoked
     * @param methodName  the name of the method to be invoked
     * @param paramTypes  the types of the parameters of the method to be invoked
     * @param args  the actual parameters to be passed to the method
     * @return the return value of the invoked method
     * @throws NoSuchMethodException
     * @throws InvocationTargetException
     * @throws IllegalAccessException
     */
    public static Object invokeMethod(Object object, String methodName, Class[] paramTypes, Object[] args)
        throws NoSuchMethodException, InvocationTargetException, IllegalAccessException {
        Class c = object.getClass();
        Method m = c.getMethod(methodName, paramTypes);
        m.setAccessible(true); // nasty, no privacy
        return m.invoke(object, args);
    }

    /**
     * Invokes a static method.
     *
     * @param className  the name of the class where the method is implemented
     *  (with full prefix, e.g. "java.util.Collections")
     * @param methodName  the name of the method to be invoked, e.g. "list"
     * @param paramTypes  the types of the parameters of the method to be invoked
     * @param args  the actual parameters to be passed to the method
     * @return the return value of the invoked method
     * @throws ClassNotFoundException
     * @throws NoSuchMethodException
     * @throws IllegalAccessException
     * @throws InvocationTargetException
     */
    public static Object invokeStaticMethod(String className, String methodName, Class[] paramTypes, Object[] args)
        throws ClassNotFoundException, NoSuchMethodException, IllegalAccessException, InvocationTargetException {
        Class c = MethodInvoker.classLoader.loadClass(className);
        Method m = c.getMethod(methodName, paramTypes);
        m.setAccessible(true); // nasty, no privacy
        return m.invoke(null, args);
    }
}
