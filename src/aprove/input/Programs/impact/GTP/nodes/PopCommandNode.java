package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

@SuppressWarnings("javadoc")
public class PopCommandNode extends CommandNode {

    private final VariableNode variable;

    public PopCommandNode(
        final String text,
        final int line,
        final int position,
        final String label,
        final VariableNode variable)
    {
        super(text, line, position, label);
        this.variable = variable;
    }

    @Override
    protected String commandText() {
        return "POP " + this.variable.toString();
    }

    public String getVariableId() {
        return this.variable.toString();
    }

    public VariableNode getVariable() {
        return this.variable;
    }

    @Override
    public HashSet<String> getVariableNames() {
        return this.variable.getVariableNames();
    }

    @Override
    public HashSet<String> getRef() {
        return new HashSet<>();
    }

    @Override
    public String getDef() {
        return this.variable.toString();
    }
}
