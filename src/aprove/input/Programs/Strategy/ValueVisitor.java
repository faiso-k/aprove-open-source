package aprove.input.Programs.Strategy;

public interface ValueVisitor<T> {
    public T visit(StringValue stringValue);

    public T visit(NumberValue numberValue);

    public T visit(ComplexValue complexValue);
}
