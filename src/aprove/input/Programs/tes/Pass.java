package aprove.input.Programs.tes;

import java.util.*;

import aprove.input.Generated.tes.analysis.*;
import aprove.input.Generated.tes.node.*;
import aprove.input.Utility.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** Base class for the three passes of the TES parser.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

class Pass extends DepthFirstAdapter {

    protected Program prog;
    protected Set gvars;
    protected Sort poly;
    protected boolean cond;
    protected ParseErrors errors;

    @Override
    public void inARulelist(ARulelist node) {
    this.cond = true;
    }
    @Override
    public void outARulelist(ARulelist node) {
    this.cond = false;
    }

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
    public Set getVars() {
    return this.gvars;
    }
    public void setVars(Set gvars) {
    this.gvars = gvars;
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
