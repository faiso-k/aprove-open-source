package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

@SuppressWarnings("javadoc")
public class AssignCommandNode extends CommandNode {
    private final NumericExpressionNode expression;

    private final VariableNode variable;

    public AssignCommandNode(
        final String text,
        final int line,
        final int position,
        final String label,
        final VariableNode variable,
        final NumericExpressionNode exp)
    {
        super(text, line, position, label);
        this.expression = exp;
        this.variable = variable;
    }

    @Override
    protected String commandText() {
        return this.variable.toString() + " = " + this.expression.toString();
    }

    public VariableNode getVariable() {
        return this.variable;
    }

    public String getVariableId() {
        return this.variable.toString();
    }

    public NumericExpressionNode getAssignedExpression() {
        return this.expression;
    }

    public BooleanExpressionNode toBooleanExpressionNode() {
        return new BinaryBooleanExpressionNode(
            null,
            0,
            0,
            this.variable,
            this.expression,
            BinaryBooleanExpressionNode.Type.EQUAL);
    }

    @Override
    public HashSet<String> getVariableNames() {
        final HashSet<String> result = (HashSet<String>) this.expression.getVariableNames().clone();
        // result.addAll(this.variable.getVariableNames()); //  debug??
        return result;
    }

    @Override
    public String getDef() {
        return this.variable.toString();
    }

    @Override
    public HashSet<String> getRef() {
        return this.expression.getVariableNames();
    }
}
