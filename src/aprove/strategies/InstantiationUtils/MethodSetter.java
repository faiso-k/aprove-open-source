package aprove.strategies.InstantiationUtils;

import java.lang.reflect.*;

import aprove.strategies.Util.*;

class MethodSetter implements Setter {
    private Method method;

    public MethodSetter(Method method) {
        this.method = method;
    }

    @Override
    public Class<?> getExpectedType() {
        return this.method.getParameterTypes()[0];
    }

    @Override
    public void set(Object target, Object value) throws UnexpectedParamMgrException {
        try {
            this.method.invoke(target, value);
        } catch (IllegalArgumentException e) {
            throw new UnexpectedParamMgrException(e);
        } catch (IllegalAccessException e) {
            throw new UnexpectedParamMgrException(e);
        } catch (InvocationTargetException e) {
            throw new UnexpectedParamMgrException(e);
        }
    }

    @Override
    public String toString() {
        return this.method.toGenericString();
    }
}
