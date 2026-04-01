package aprove.input.Programs.Strategy;

public interface StrategyElementVisitor extends DeclarationVisitor, ValueVisitor<Void>, ExpressionVisitor<Void>{
    public void visit(RawModule rawModule);

    @Override
    public void visit(ClassDeclaration classDeclaration);

    public void visit(Parameters parameters);

    @Override
    public void visit(LetDeclaration letDeclaration);

    @Override
    public Void visit(FunctionExpression functionExpression);

    @Override
    public Void visit(GenericExpression genericExpression);

    public void visit(ExpressionList expressionList);

    @Override
    public Void visit(StringValue stringValue);

    @Override
    public Void visit(NumberValue numberValue);

    @Override
    public Void visit(ComplexValue complexValue);
}
