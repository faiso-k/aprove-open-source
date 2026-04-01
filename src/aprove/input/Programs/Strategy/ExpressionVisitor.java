package aprove.input.Programs.Strategy;

public interface ExpressionVisitor<T> {

    T visit(FunctionExpression functionExpression);

    T visit(GenericExpression genericExpression);

}
