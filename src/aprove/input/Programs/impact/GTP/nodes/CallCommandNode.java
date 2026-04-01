package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

public class CallCommandNode extends CommandNode {

    private final LabelNode callId;
    private final String function;

    public CallCommandNode(
        final String text,
        final int line,
        final int position,
        final String label,
        final LabelNode callId,
        final String function)
    {
        super(text, line, position, label);

        this.callId = callId;
        this.function = function;
    }

    @Override
    protected String commandText() {
        return "CALL " + this.callId.toString();
    }

    public String getCallId() {
        return this.callId.toString();
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
