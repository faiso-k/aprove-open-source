package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

public class AssumeCommandNode extends CommandNode {
    BooleanExpressionNode exp;

    public AssumeCommandNode(
        final String text,
        final int line,
        final int position,
        final String label,
        final BooleanExpressionNode exp)
    {
        super(text, line, position, label);
        this.exp = exp;
    }

    @Override
    protected String commandText() {
        return "ASSUME\t" + this.exp.toString();
    }

    public BooleanExpressionNode getAssumption() {
        return this.exp;
    }

    @Override
    public HashSet<String> getRef() {
        return this.exp.getVariableNames();
    }

    @Override
    public HashSet<String> getVariableNames() {
        return this.exp.getVariableNames();
    }

}
