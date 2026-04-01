package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

public class LabelNode extends Node {
    final String id;
    final Type type;
    final String tag;

    public LabelNode(
        final String text,
        final int line,
        final int pos,
        final String id,
        final Type type,
        final String tag)
    {
        super(text, line, pos);

        this.id = id;
        this.type = type;
        this.tag = tag;
    }

    public LabelNode(
        final String text,
        final int line,
        final int pos,
        final String id,
        final Type type,
        final int number)
    {
        super(text, line, pos);

        this.id = id;
        this.type = type;
        this.tag = String.valueOf(number);
    }

    public LabelNode(final String id, final Type type, final int number) {
        super("", 0, 0);

        this.id = id;
        this.type = type;
        this.tag = String.valueOf(number);
    }

    @Override
    public String toString() {
        return this.type.getSymbol()
            + LabelNode.DELIMITER_PREF
            + this.id
            + (this.type.isTagged() ? LabelNode.DELIMITER + this.tag : "");
    }


    @Override
    public HashSet<String> getVariableNames() {
        return new HashSet<>();
    }

    public enum Type {
        NONE("NONE"),
        USER_DEFINED("USR", true),
        FUNCTION_BEGIN("FBEGIN"),
        FUNCTION_END("FEND"),
        WHILE_CONDITION(
            "WCOND",
            true), WHILE_BREAK("WBREAK", true), FOR_CONDITION("FCOND", true), FOR_BREAK("FBREAK", true), IF_CONDITION(
                "ICOND",
                true), ELSE_BLOCK("EBLOCK", true), IF_BREAK("IBREAK", true), CALL_RETURN("RETURN", true);

        private String symbol;
        private boolean tagged;

        private Type(final String s) {
            this.symbol = s;
            this.tagged = false;
        }

        private Type(final String s, final boolean numbered) {
            this.symbol = s;
            this.tagged = numbered;
        }


        public String getSymbol() {
            return this.symbol;
        }

        public boolean isTagged() {
            return this.tagged;
        }
    }

    private static String DELIMITER = "_";
    private static String DELIMITER_PREF = "^";
}
