package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

@SuppressWarnings("javadoc")
public class BranchCommandNode extends CommandNode {
    LabelNode brabchLabel;

    public BranchCommandNode(
        final String text,
        final int line,
        final int position,
        final String label,
        final LabelNode labelNode)
    {
        super(text, line, position, label);

        this.brabchLabel = labelNode;
    }

    @Override
    protected String commandText() {
        return "GOTO " + this.brabchLabel.toString();
    }

    @Override
    public HashSet<String> getVariableNames() {
        return new HashSet<String>();
    }

    public String getBranchLabel() {
        return this.brabchLabel.toString();
    }

    @Override
    public HashSet<String> getRef() {
        return new HashSet<>();
    }
}
