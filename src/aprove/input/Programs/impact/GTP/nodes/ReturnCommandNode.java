package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

/**
 * @author marinag
 *
 */
public class ReturnCommandNode extends CommandNode {
    private final String function;

    @SuppressWarnings("javadoc")
    public ReturnCommandNode(
        final String text,
        final int line,
        final int position,
        final String label,
        final String function)
    {
        super(text, line, position, label);
        this.function = function;
    }

    @Override
    protected String commandText() {
        return "RETURN";
    }

    public String getFunction() {
        return this.function;
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
