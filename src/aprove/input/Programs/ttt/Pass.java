package aprove.input.Programs.ttt;

import java.util.*;

import aprove.input.Generated.ttt.analysis.*;
import aprove.input.Generated.ttt.node.*;
import aprove.input.Utility.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/** Base class for the three passes of the TES parser.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

class Pass extends DepthFirstAdapter {

    protected Program prog;
    protected Set gvars;
    protected Sort poly;
    protected boolean cond;
    protected FreshNameGenerator infixes;
    protected ParseErrors errors;

    public String escape(String old) {
        return this.infixes.getFreshName(old, true);
    }

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
    this.poly = prog.getSort("^");
    this.prog = prog;
    }
    public Set getVars() {
    return this.gvars;
    }
    public void setVars(Set gvars) {
    this.gvars = gvars;
    }
    public void initVars(Start tree) {
        GetVars gv = new GetVars();
        gv.setVars(new HashSet());
        tree.apply(gv);
        this.gvars = gv.getVars();
    }
    public FreshNameGenerator getInfixes() {
        return this.infixes;
    }
    public void setInfixes(FreshNameGenerator infixes) {
        this.infixes = infixes;
    }
    public void initInfixes(Start tree) {
        GetSignature gs = new GetSignature();
    tree.apply(gs);
    this.infixes = new FreshNameGenerator(gs.getSignature(), FreshNameGenerator.TTT_FUNCS);
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
