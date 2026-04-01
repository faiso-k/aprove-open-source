package aprove.strategies.Parameters;

import java.lang.reflect.*;
import java.util.*;

import aprove.strategies.InstantiationUtils.*;
import aprove.strategies.Util.*;

public class ObjectCreator {
    private final StrategyProgram program;

    public ObjectCreator(StrategyProgram context) {
        this.program = context;
    }

    public Object build(String name, FrozenParameters params,
            NameDefinition decl) throws ParameterManagerException {
        Class<?> childClass = decl.getDefinedClass();

        // If a name is set equal to an enum class, instead of instantiating the enum
        // (which makes no sense), get the enum constant with the same name as the LHS.
        if (childClass.isEnum()){
            return ReflectUtil.retrieveEnum(childClass, name);
        }

        FrozenParameters defaults = decl.getDefaults();

        StrategyCreator creator = CreatorBuilder.stratCreatorFor(childClass);

        if (params != null) {
            this.setParameters(creator, params, defaults, childClass);
        }

        return creator.getInstance();
    }

    private void setParameters(StrategyCreator creator, FrozenParameters parameters,
            FrozenParameters defaults, Class<?> targetClass)
            throws WrappedParamMgrException {

        for (Map.Entry<String, ParamValue> param : defaults.entries()) {
            if (! parameters.containsKey(param.getKey())) {
                this.setParam(param, creator, targetClass, "setting default ");
            }
        }
        for (Map.Entry<String, ParamValue> param : parameters.entries()) {
            this.setParam(param, creator, targetClass, "while setting ");
        }
        try {
            creator.acceptStrategies(parameters.getSubStrategies());
        } catch (ParameterManagerException e) {
            throw new WrappedParamMgrException("While passing strategy parameters", e);
        }
    }

    private void setParam(Map.Entry<String, ParamValue> param,
            StrategyCreator creator, Class<?> targetClass, String errmsg) throws WrappedParamMgrException {
        String parameterName = param.getKey();
        try {
            ParamValue value = param.getValue();
            Class<?> argumentClass = creator.getParameterClass(parameterName);

            Object asObject = value.getOrCoerce(this.program, argumentClass, targetClass);
            creator.setParameter(parameterName, asObject);
        } catch (ParameterManagerException e) {
            throw new WrappedParamMgrException(errmsg + param, e);
        }
    }

    public static Object coerce(Class<?> targetClass,
            String value, Class<?> parameterClass) throws UnexpectedParamMgrException, UserErrorException {

        // First, try finding a field by that name.
        Field f = ReflectUtil.findField(targetClass, value);
        if (f != null) {
            return ReflectUtil.readField(f);
        }

        // If that doesn't help, try coercing somehow.
        if (parameterClass.isPrimitive()) {
            return ReflectUtil.convertToPrimitiveType(parameterClass, value);
        } else if (parameterClass.isEnum()) {
            return ReflectUtil.retrieveEnum(parameterClass, value);
        } else if (parameterClass.equals(String.class)) {
            return value;
        }

        Method m = ReflectUtil.getValueOf_Method(parameterClass);
        if (m != null) {
            return ReflectUtil.callStaticMethod(m, value);
        }

        throw new UserErrorException("cannot find '" + value + "' " +
                "in properties file or in a static field, and cannot coerce.\n" +
                "You are probably missing an entry in std.strategy.");
    }

}
