package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

@SuppressWarnings("javadoc")
public class StopCommandNode extends CommandNode {

    public StopCommandNode(final String text, final int line, final int position, final String label) {
        super(text, line, position, label);
    }

    @Override
    protected String commandText() {
        return "STOP";
    }

    @Override
    public HashSet<String> getVariableNames() {
        return new HashSet<>();
    }

    @Override
    public HashSet<String> getRef() {
        return new HashSet<>();
    }

}
