package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

/**
 * @author marinag
 *
 */
public class AbortCommandNode extends CommandNode {
    @SuppressWarnings("javadoc")
    public AbortCommandNode(final String text, final int line, final int position, final String label) {
        super(text, line, position, label);
    }

    @Override
    protected String commandText() {
        return "ABORT";
    }

    @Override
    public HashSet<String> getVariableNames() {
        return new HashSet<String>();
    }



    @Override
    public HashSet<String> getRef() {
        return new HashSet<String>();
    }
}
