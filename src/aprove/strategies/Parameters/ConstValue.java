package aprove.strategies.Parameters;

public class ConstValue implements ParamValue {
    private final Object contents;

    public ConstValue(Object contents) {
        this.contents = contents;
    }

    @Override
    public Object getOrCoerce(StrategyProgram program, Class<?> expectedClass,
            Class<?> targetClass) {
        if (expectedClass.equals(Boolean.class) && this.contents instanceof String) {
            System.err.println("Implicitly converting string literal to boolean. Fix your strategy!");
            return Boolean.valueOf((String)this.contents);
        }
        return this.contents;
    }

    @Override
    public Object get(StrategyProgram program) {
        return this.contents;
    }

    @Override
    public String toString() {
        if (this.contents instanceof String) {
            return "\"" + this.contents + "\"";
        }
        if (this.contents == null) {
            return "Null";
        }
        return this.contents.toString();
    }
}
