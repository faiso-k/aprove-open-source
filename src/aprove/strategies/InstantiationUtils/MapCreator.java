package aprove.strategies.InstantiationUtils;

import java.util.*;

import aprove.strategies.Util.*;

public class MapCreator implements ParametrizedCreator {
    private Map<String, Object> backend;

    @SuppressWarnings("unchecked")
    public MapCreator(Class<?> targetClass) throws UnexpectedParamMgrException {
        try {
            this.backend = (Map<String, Object>) targetClass.newInstance();
        } catch (InstantiationException e) {
            throw new UnexpectedParamMgrException(e);
        } catch (IllegalAccessException e) {
            throw new UnexpectedParamMgrException(e);
        }
    }

    @Override
    public Class<Object> getParameterClass(String name)
            throws UnexpectedParamMgrException {
        return Object.class;
    }

    @Override
    public void setParameter(String name, Object value)
            throws UnexpectedParamMgrException {
        this.backend.put(name, value);
    }

    @Override
    public Object getInstance() throws UnexpectedParamMgrException {
        return this.backend;
    }

}
