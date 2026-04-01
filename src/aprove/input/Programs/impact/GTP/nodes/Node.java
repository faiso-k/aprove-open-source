package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

@SuppressWarnings("javadoc")
public abstract class Node {
    private final String text;
    private final int line;
    private final int position;

    public Node(final String text, final int line, final int pos) {
        this.text = text;
        this.line = line;
        this.position = pos;
    }

    public int getLine() {
        return this.line;
    }

    public int getPos() {
        return this.position;
    }

    public String getText() {
        return this.text;
    }

    @Override
    public abstract String toString();

    public abstract HashSet<String> getVariableNames();
    /*    {
            return new HashSet<>();
        }*/
}
