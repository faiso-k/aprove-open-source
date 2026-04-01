package aprove.input.Programs.Strategy;

import java.util.*;

public abstract class ParameterFactory {
    public static Parameters fromMap(Map<String, Value> map) {
        return new Parameters(map);
    }

    public static Parameters empty() {
        return Parameters.EMPTY;
    }

    public static Value number(int wrapped) {
        return new NumberValue(wrapped);
    }

    public static Value literalString(String literalString) {
        return new StringValue(literalString);
    }

    public static Value callValue(String funcName, Parameters params) {
        if (params == null) {
            params = Parameters.EMPTY;
        }
        return new ComplexValue(funcName, params);
    }

    public static String unquote(String quotedString) {
        return quotedString.substring(1, quotedString.length() - 1);
    }
}
