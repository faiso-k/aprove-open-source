package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

@SuppressWarnings("javadoc")
public class PushCommandNode extends CommandNode {

    private final VariableNode var;

    public PushCommandNode(
        final String text,
        final int line,
        final int position,
        final String label,
        final VariableNode var)
    {
        super(text, line, position, label);
        this.var = var;
    }

    @Override
    protected String commandText() {
        return "PUSH " + this.var.toString();
    }

    /* public String getVariableId() {
         return this.variable.toString();
     }*/

    public VariableNode getVariable() {
        return this.var;
    }


    @Override
    public HashSet<String> getVariableNames() {
        return this.var.getVariableNames();
    }

    @Override
    public HashSet<String> getRef() {
        return new HashSet<>();
    }

    @Override
    public String getDef() {
        return null; //this.variable.toString();
    }
}
