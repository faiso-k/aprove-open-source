package aprove.input.Programs.Strategy;

import java.util.*;

public abstract class ExpressionFactory {
    public static StrategyExpression sequence(final StrategyExpression e1, final StrategyExpression e2) {
        return new BinaryExpression("Sequence", ":", e1, e2);
    }

    public static StrategyExpression parSequence(final StrategyExpression e1, final StrategyExpression e2) {
        return new BinaryExpression("ParallelSequence", ";", e1, e2);
    }

    public static StrategyExpression star(final StrategyExpression e) {
        return new PostfixExpression("_Star", "*", e);
    }

    public static StrategyExpression plus(final StrategyExpression e) {
        return new PostfixExpression("_Plus", "+", e);
    }

    public static StrategyExpression question(final StrategyExpression e) {
        return new PostfixExpression("_Question", "?", e);
    }


    public static StrategyExpression letRef(final String name) {
        return new FunctionExpression(name);
    }

    public static StrategyExpression classRef(final String name, Parameters params, List<StrategyExpression> spars) {
        if (spars == null) {
            spars = Collections.emptyList();
        }
        if (params == null) {
            params = Parameters.EMPTY;
        }
        return new GenericExpression(name, params, spars);
    }

    public static StrategyExpression repeat(final int min,
            final int max,
            final StrategyExpression exp) {
        final Map<String, Value> p = new HashMap<String, Value>();
        p.put("Min", new NumberValue(min));
        if (max != -1) {
            p.put("Max", new NumberValue(max));
        }
        return new GenericExpression("Repeat", new Parameters(p),
                Collections.singletonList(exp));
    }

    public static StrategyExpression repeatS(final int min,
            final int max,
            final StrategyExpression exp) {
        final Map<String, Value> p = new HashMap<String, Value>();
        if (min != 0) {
            p.put("Min", new NumberValue(min));
        }
        if (max != -1) {
            p.put("Max", new NumberValue(max));
        }
        return new GenericExpression("RepeatS", new Parameters(p),
                Collections.singletonList(exp));
    }

    public static StrategyExpression wallTimer(final int timeout, final StrategyExpression exp) {
        final Map<String, Value> p = new HashMap<String, Value>();
        p.put("Timeout", new NumberValue(timeout));
        return new GenericExpression("WallTimer", new Parameters(p),
                Collections.singletonList(exp));
    }

    public static StrategyExpression timer(final int timeout, final StrategyExpression exp) {
        final Map<String, Value> p = new HashMap<String, Value>();
        p.put("Timeout", new NumberValue(timeout));
        return new GenericExpression("Timer", new Parameters(p),
                Collections.singletonList(exp));
    }

    public static StrategyExpression delay(final int delay, final StrategyExpression exp) {
        final Map<String, Value> p = new HashMap<String, Value>();
        p.put("Delay", new NumberValue(delay));
        return new GenericExpression("Delay", new Parameters(p),
                Collections.singletonList(exp));
    }

    public static StrategyExpression anyDelay(final int delay, List<StrategyExpression> el) {
        if (el == null) {
            el = Collections.emptyList();
        }
        final Map<String, Value> p = new HashMap<String, Value>();
        p.put("Delay", new NumberValue(delay));
        return new GenericExpression("AnyDelay", new Parameters(p), el);
    }

    public static StrategyExpression anyK(final int k, List<StrategyExpression> el) {
        if (el == null) {
            el = Collections.emptyList();
        }
        final Map<String, Value> p = new HashMap<String, Value>();
        p.put("parallelStrategies", new NumberValue(k));
        return new GenericExpression("AnyK", new Parameters(p), el);
    }
}
