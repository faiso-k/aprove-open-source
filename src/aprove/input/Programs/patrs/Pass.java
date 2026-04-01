package aprove.input.Programs.patrs;

import aprove.input.Generated.patrs.analysis.*;
import aprove.input.Generated.patrs.node.*;
import aprove.input.Utility.*;

abstract class Pass extends DepthFirstAdapter {
    protected ParseErrors errors;

    public void setErrors(ParseErrors errors) {
        this.errors = errors;
    }

    public ParseErrors getErrors() {
        return this.errors;
    }

    public void addParseError(Token t, int level, String msg) {
        ParseError pe = new ParseError(level);
        pe.setToken(this.chop(t));
        pe.setPosition(t.getLine(), t.getPos());
        pe.setMessage(msg);
        this.errors.add(pe);
    }

    protected String chop(Node node) {
        return node.toString().trim();
    }

}
