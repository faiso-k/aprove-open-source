package aprove.input.Programs.ipad;

import java.util.*;

import aprove.input.Generated.ipad.analysis.*;
import aprove.input.Generated.ipad.node.*;
import aprove.input.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

/** Base class for the passes of the ipad-parser.
 * @author Christian Haselbach
 * @version $Id$
 */

abstract class Pass extends DepthFirstAdapter {

    // magic type/sort, matches any type/sort => do not use in programs!
    protected static final String ANY_TYPE_NAME = "IPAD_ANY_TYPE";
    protected static final String ANY_SORT_NAME = "IPAD_ANY_SORT";
    protected static final AlgebraTerm ANY_TYPE = AlgebraVariable.create(VariableSymbol.create(Pass.ANY_TYPE_NAME));
    protected static final Sort ANY_SORT = Sort.create(Pass.ANY_SORT_NAME);

    protected boolean containsInts;

    protected ParseErrors errors;
    protected Program prog;
    protected Hashtable procHeads;
    protected Hashtable witnessTerms; // if sorts are obsolete remove this element
    // A hashtable containing sorts and the corresponding tokens.
    protected Hashtable sorttoken;  // if sorts are obsolete do not remove this element
    protected TypeContext typeContext;

    public Pass set(Pass pass) {
    this.setErrors(pass.getErrors());
    this.setProgram(pass.getProgram());
    this.setProcHeads(pass.getProcHeads());
    this.setWitnessTerms(pass.getWitnessTerms());
    this.setSorttoken(pass.getSorttoken());
    this.setTypeContext(pass.getTypeContext());
    this.containsInts = pass.containsInts;
    return this;
    }

    public void setProgram(Program prog) {
    this.prog = prog;
    }

    public void setTypeContext(TypeContext typeContext){
        this.typeContext = typeContext;
    }

    public TypeContext getTypeContext(){
        return this.typeContext;
    }

    public Program getProgram() {
    return this.prog;
    }

    public void setWitnessTerms(Hashtable wt) {
    this.witnessTerms = wt;
    }

    public Hashtable getWitnessTerms() {
    return this.witnessTerms;
    }

    public void setProcHeads(Hashtable t) {
    this.procHeads = t;
    }

    public Hashtable getProcHeads() {
    return this.procHeads;
    }

    public void setErrors(ParseErrors errs) {
    this.errors = errs;
    }

    public ParseErrors getErrors() {
    return this.errors;
    }

    public void setSorttoken(Hashtable st) {
    this.sorttoken = st;
    }

    public Hashtable getSorttoken() {
    return this.sorttoken;
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

    protected String chop(Node node) {
    return node.toString().trim();
    }

    protected AlgebraTerm getDeclaredType(String name,Token t) {
    TypeDefinition td = this.typeContext.getTypeDef(name);
    if (td == null) {
        this.addParseError(t, "undeclared type '"+this.chop(t)+"'");
        return null;
    }
    return td.getDefTerm();
    }

    protected boolean checkdeclared(Sort s, Token t) {
    if (s == null) {
        this.addParseError(t, "undeclared sort ''"+this.chop(t)+"''");
        return false;
    }
    return true;
    }


    protected boolean checkTypes(AlgebraTerm type1, AlgebraTerm type2, Token t) {
        // the type ANY_TYPE always fits
        if ( (type1 == Pass.ANY_TYPE) || (type2 == Pass.ANY_TYPE) ) {
            return true;
        }

        if (type1 == null) {
            return true;
        }
        if (type2 == null || !type1.equals(type2)) {
            String msg = "type ''"+type1.getSymbol().getName()+"'' expected, but ''";
            msg += (type2 == null) ? "void" : type2.getSymbol().getName();
            msg += "'' found";
            this.addParseError(t, msg);
            return false;
        }
        return true;
    }


    // TODO remove me
    protected boolean checksorts(Sort s1, Sort s2, Token t) {
    // the sort ANY_SORT always fits
    if ( (s1 == Pass.ANY_SORT) || (s2 == Pass.ANY_SORT) ) {
        return true;
    }

    if (s1 == null) {
        return true;
    }
    if (s2 == null || s1 != s2) {
        String msg = "sort ''"+s1.getName()+"'' expected, but ''";
        msg += s2 == null ? "void" : s2.getName();
        msg += "'' found";
        this.addParseError(t, msg);
        return false;
    }
    return true;
    }

     protected void concatStmtlists(PNeStatementlist sl1, PNeStatementlist sl2) {
    PNeStatementlist next = ((ANeStatementlist) sl1).getNeStatementlist();
    while (next != null) {
        sl1 = next;
        next = ((ANeStatementlist) sl1).getNeStatementlist();
    }
    ((ANeStatementlist) sl1).setNeStatementlist(sl2);
    }

    protected static PNeStatementlist getStatementlist(PStatementlist sl) {
    try {
        return ((ANonEmptyStatementlist)sl).getNeStatementlist();
    }
    catch (ClassCastException e) {
        return null;
    }
    }
}
