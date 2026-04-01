package aprove.strategies.Parameters;

import aprove.strategies.Util.*;

public interface ParamValue {
    public Object getOrCoerce(StrategyProgram program, Class<?> expectedClass, Class<?> targetClass) throws ParameterManagerException;

    public Object get(StrategyProgram program) throws WrappedParamMgrException;
}
