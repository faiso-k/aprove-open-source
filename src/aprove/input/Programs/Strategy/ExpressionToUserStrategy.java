package aprove.input.Programs.Strategy;

import java.util.*;

import aprove.strategies.Parameters.*;
import aprove.strategies.UserStrategies.*;

public class ExpressionToUserStrategy implements ExpressionVisitor<UserStrategy> {
    public static final ExpressionVisitor<UserStrategy> INSTANCE = new ExpressionToUserStrategy();

    @Override
    public UserStrategy visit(FunctionExpression expr) {
        return new VariableStrategy(expr.name);
    }

    @Override
    public UserStrategy visit(GenericExpression expr) {
        String name = expr.name;
        Parameters params = expr.params;
        List<StrategyExpression> subexpressions = expr.subexpressions.exps;
        List<UserStrategy> strategies = null;
        if (subexpressions.size() > 0) {
            strategies = new ArrayList<UserStrategy>(subexpressions.size());
            for(StrategyExpression e: subexpressions) {
                strategies.add(e.accept(this));
            }
        }
        FrozenParameters frozen = ValueToParamValue.freeze(params, strategies);
        FuncValue value = new FuncValue(name, frozen);
        return new LazyStrategy(value);
    }
}
