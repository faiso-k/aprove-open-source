package aprove.input.Programs.Strategy;

import immutables.*;

public interface StrategyExpression extends Immutable, PrettyPrintable {

    public <T> T accept(ExpressionVisitor<T> visitor);

}
