package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

@SuppressWarnings("javadoc")
public abstract class CommandNode extends Node {

    private String label = null;
    private String origianlText = null;
    private HashSet<String> avaliableVariables;

    public CommandNode(final String text, final int line, final int position, final String label) {
        super(text, line, position);
        this.label = label;
    }

    public void setOriginalText(final String text) {
        this.origianlText = text;
    }

    public String getOriginalText() {
        return this.origianlText;
    }

    public void setLabel(final String label) {
        this.label = label;
    }

    public String getLabel() {
        return this.label;
    }

    @Override
    public final String toString() {
        return String.format("%1$-" + 30 + "s", this.label == null ? "" : (this.label + ":"), 30)
            + this.commandText();
    }

    protected abstract String commandText();

    public String getDef() {
        return null;
    }

    public abstract HashSet<String> getRef();

    public HashSet<String> setAvaliableVariables(final HashSet<String> avaliableVariables) {
        return this.avaliableVariables = avaliableVariables;
    }

    public HashSet<String> getAvaliableVariables() {
        return this.avaliableVariables;
    }

}
