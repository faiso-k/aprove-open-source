package aprove.strategies.InstantiationUtils;

import java.util.*;

import aprove.strategies.UserStrategies.*;
import aprove.strategies.Util.*;

public abstract class StrategyCreator implements ParametrizedCreator {
    private final ParametrizedCreator backend;

    public StrategyCreator(ParametrizedCreator backend) {
        this.backend = backend;
    }

    @Override
    public Class<?> getParameterClass(String name)
            throws ParameterManagerException {
        return this.backend.getParameterClass(name);
    }

    @Override
    public void setParameter(String name, Object value)
            throws ParameterManagerException {
        this.backend.setParameter(name, value);
    }

    @Override
    public Object getInstance() throws ParameterManagerException {
        return this.backend.getInstance();
    }

    public abstract void acceptStrategies(List<UserStrategy> subStrategies) throws ParameterManagerException;

}
