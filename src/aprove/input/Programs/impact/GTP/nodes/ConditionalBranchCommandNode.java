package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

@SuppressWarnings("javadoc")
public class ConditionalBranchCommandNode extends BranchCommandNode {

    private BooleanExpressionNode expression = null;

    public ConditionalBranchCommandNode(
        final String text,
        final int line,
        final int position,
        final String label,
        final LabelNode labelNode,
        final BooleanExpressionNode exp)
    {
        super(text, line, position, label, labelNode);
        this.expression = exp;
    }

    @Override
    protected String commandText() {
        return (this.expression == null ? "" : "IF (" + this.expression.toString() + ") ") + super.commandText();

    }

    public BooleanExpressionNode getCondition() {
        return this.expression;
    }

    @Override
    public HashSet<String> getVariableNames() {
        return this.expression.getVariableNames();
    }

    @Override
    public HashSet<String> getRef() {
        return this.expression.getVariableNames();
    }

}
