package aprove.input.Programs.Strategy;

import java.util.*;

import aprove.strategies.Parameters.*;
import aprove.strategies.UserStrategies.*;

public class ValueToParamValue implements ValueVisitor<ParamValue>{
    public static final ValueVisitor<ParamValue> INSTANCE = new ValueToParamValue();

    @Override
    public ParamValue visit(StringValue val) {
        return new ConstValue(val.value);
    }

    @Override
    public ParamValue visit(NumberValue val) {
        return new ConstValue(val.value);
    }

    @Override
    public ParamValue visit(ComplexValue complexValue) {
        return new FuncValue(complexValue.identifier, ValueToParamValue.freeze(complexValue.params));
    }

    public static FrozenParameters freeze(Parameters params) {
        return ValueToParamValue.freeze(params, null);
    }

    public static FrozenParameters freeze(Parameters params, List<UserStrategy> strategies) {
        return new FrozenParameters(ValueToParamValue.toMap(params), strategies);
    }

    public static Map<String, ParamValue> toMap(Parameters defaults) {
        Map<String, ParamValue> result = new HashMap<String, ParamValue>();
        for(Map.Entry<String, Value> e: defaults.getMap().entrySet()) {
            ParamValue asParam = e.getValue().accept(ValueToParamValue.INSTANCE);
            result.put(e.getKey(), asParam);
        }
        return result;
    }
}
