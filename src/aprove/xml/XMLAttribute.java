package aprove.xml;

import org.w3c.dom.*;

public enum XMLAttribute {
    ARITY("arity"),
    FUNNAME("name"),
    VARNAME("name"),
    SHARP("sharp"),

    VALUE("value"),

    DP_EDGE_FROM("fr"),
    DP_EDGE_TO("to"),

    RULE_IDENTIFIER("identifier"),
    TYPE("type"),

    STRICT("strict"),
    EXACTLY_INNERMOST("exactly"),

    DIMENSION("dimension"),
    MATRO_TYPE("type"),
    BELOW_ZERO("belowZero"),

    COLLAPSE("collapse"),

    QUASI("quasi"),

    OBL_IDENTIFIER("identifier"),
    COMMIT_ID("commit-id"),

    IMPLICATION_VALUE("value"),

    MATCH("match"),
    BOUND("bound"),
    ;

    private final String attribute;

    private XMLAttribute(String attribute) {
        this.attribute = attribute;
    }

    public final void setAttribute(Element elem, String value) {
        elem.setAttribute(this.attribute, value);
    }
}
