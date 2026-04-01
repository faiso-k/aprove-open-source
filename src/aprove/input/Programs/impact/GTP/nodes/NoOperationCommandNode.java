package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

@SuppressWarnings("javadoc")
public class NoOperationCommandNode extends CommandNode {

    public NoOperationCommandNode(final String text, final int line, final int position, final String label) {
        super(text, line, position, label);
    }

    @Override
    protected String commandText() {
        return "NOP";
    }

    /*
    @Override
    public HashSet<String> getVariablesId() {
        return new HashSet<>();
    }*/

    @Override
    public HashSet<String> getVariableNames() {
        return new HashSet<>();
    }

    @Override
    public HashSet<String> getRef() {
        return new HashSet<>();
    }
}
