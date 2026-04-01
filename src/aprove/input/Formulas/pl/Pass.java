package aprove.input.Formulas.pl;

import aprove.input.Generated.pl.analysis.*;
import aprove.input.Generated.pl.node.*;
import aprove.input.Utility.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** Helper-class for the conversion of an ast to the internal formula representation.
 * @author Stephan Falke, Christian Haselbach
 * @version $Id$
 */

class Pass extends DepthFirstAdapter {

    protected Formula formula;
    protected Program prog;
    protected ParseErrors errors;

    public Pass() {
        this.errors = new aprove.input.Utility.ParseErrors();
    }

    protected String chop(Node node) {
    return node.toString().trim();
    }

    public Program getProgram() {
    return this.prog;
    }

    public void setProgram(Program prog) {
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
    protected boolean checksorts(Sort s1, Sort s2, Token t) {
    if (s1 != s2) {
        this.addParseError(t, "sort '"+s1.getName()+"' expected, not '"+ s2.getName()+"'");
        return false;
    }
    return true;
    }

    public void setContext(Program context) {
        this.prog = context;
    }

    public Formula getFormula() {
        return this.formula;
    }
}
