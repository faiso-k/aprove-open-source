package aprove.input.Programs.srs;

import java.util.*;

import aprove.input.Generated.srs.analysis.*;
import aprove.input.Generated.srs.node.*;
import aprove.input.Utility.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** Base class for the three passes of the SRS parser.
 * @author Peter Schneider-Kamp, Stephan Falke
 * @version $Id$
 */

class Pass extends DepthFirstAdapter {

    protected Program prog;
    protected Set gvars;
    protected Sort poly;
    protected boolean cond;
    protected ParseErrors errors;

    protected String chop(Node node) {
    return node.toString().trim();
    }
    public Program getProgram() {
    return this.prog;
    }
    public void setProgram(Program prog) {
    this.poly = prog.getSort(Sort.standardName);
    this.prog = prog;
    }
    public void setErrors(ParseErrors errs) {
    this.errors = errs;
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

    public void addParseError(Token t, String msg) {
    this.addParseError(t, ParseError.ERROR, msg);
    }
}
