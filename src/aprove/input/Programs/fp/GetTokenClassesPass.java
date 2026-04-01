package aprove.input.Programs.fp;

import java.util.*;

import aprove.input.Generated.fppp.analysis.*;
import aprove.input.Generated.fppp.node.*;
import aprove.input.Utility.*;

/** Treewalker that implements the pre-parse-pass to get the
 *  tokens that are not in the noappid-class.
 *  @author Christian Haselbach
 *  @version $Id$
 */

class GetTokenClassesPass extends DepthFirstAdapter {

    ParseErrors errors;
    Set tokens;

    public void setErrors(ParseErrors errs) {
    this.errors = errs;
    }

    public ParseErrors getErrors() {
    return this.errors;
    }

    public void setTokens(Set s) {
    this.tokens = s;
    }

    public Set getTokens() {
    return this.tokens;
    }

    @Override
    public void caseAConstr(AConstr node) {
    if (node.getSelidlist() == null) {
        return;
    }
    Token t = node.getCons();
    String name = t.toString().trim();
    if (!this.tokens.add(name)) {
//        ParseError pe = new ParseError(ParseError.ERROR);
//        pe.setToken(name);
//        pe.setPosition(t.getLine(), t.getPos());
//        pe.setMessage("multiple definition of function ''"+name+"''");
//        this.errors.add(pe);
    }
    node.getSelidlist().apply(this);
    }

    @Override
    public void caseAFunct(AFunct node) {
    Token t = node.getFunctname();
    String name = t.toString().trim();
    if (!this.tokens.add(name)) {
//        ParseError pe = new ParseError(ParseError.ERROR);
//        pe.setToken(name);
//        pe.setPosition(t.getLine(), t.getPos());
//        pe.setMessage("multiple definition of function ''"+name+"''");
//        this.errors.add(pe);
    }
    }

    @Override
    public void caseAOpdef(AOpdef node) {
    Token t = node.getOpname();
    String name = t.toString().trim();
    if (!this.tokens.add(name)) {
//        ParseError pe = new ParseError(ParseError.ERROR);
//        pe.setToken(name);
//        pe.setPosition(t.getLine(), t.getPos());
//        pe.setMessage("multiple definition of function ''"+name+"''");
//        this.errors.add(pe);
    }
    }

    @Override
    public void inAStruct(AStruct node) {
    Token t = node.getStructname();
    String name = t.toString().trim();
    if (!this.tokens.add(name)) {
        ParseError pe = new ParseError(ParseError.ERROR);
        pe.setToken(name);
        pe.setPosition(t.getLine(), t.getPos());
        pe.setMessage("multiple definition of function ''"+name+"''");
        this.errors.add(pe);
    }
    }

    @Override
    public void caseASelector(ASelector node) {
    Token t = node.getDot();
    String name = t.toString().trim();
    if (!name.equals(".")) {
        ParseError pe = new ParseError(ParseError.ERROR);
        pe.setToken(name);
        pe.setPosition(t.getLine(), t.getPos());
        pe.setMessage("'.' expected, but "+name+" found");
        this.errors.add(pe);
        return;
    }
    t = node.getName();
    name = t.toString().trim();
    if (!this.tokens.add(name)) {
        ParseError pe = new ParseError(ParseError.ERROR);
        pe.setToken(name);
        pe.setPosition(t.getLine(), t.getPos());
        pe.setMessage("multiple definition of identifier ''"+name+"''");
        this.errors.add(pe);
    }
    }

}
