package aprove.input.Terms.term;

import java.util.*;

import aprove.input.Generated.term.analysis.*;
import aprove.input.Generated.term.node.*;
import aprove.input.Generated.term.parser.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** Treewalker that converts an abstract syntax tree to the internal term representation.
 * @author Peter Schneider-Kamp, Christian Haselbach
 * @version $Id$
 */

class Pass extends DepthFirstAdapter {

    protected AlgebraTerm term;
    protected Hashtable gvars;
    protected Sort poly;
    protected Stack<AlgebraTerm> terms;
    protected Stack<Sort> sorts;
    protected Program prog;
    protected Vector errors;

    @Override
    public void inStart(Start node) {
    this.gvars = new Hashtable();
    this.poly = this.prog.getSort(Sort.standardName);
    this.terms = new Stack<AlgebraTerm>();
    this.sorts = new Stack<Sort>();
    this.sorts.push(this.poly);
    this.errors = new Vector();
    }

    protected void checkdeclared(Sort s, Token t) {
    if (s == null) {
        this.errors.add(new ParserException(t, "undeclared sort '"+this.chop(t)+"'"));
    }
    }

    protected void checksorts(Symbol sym, Sort s1, Token t) {
    Sort s2 = sym.getSort();
    if (s1 != s2) {
        if (s2 == this.poly) {
        sym.setSort(s1);
        } else if (s1 != this.poly) {
        this.errors.add(new ParserException(t, "sort '"+s1.getName()+"' expected, not '"+s2.getName()+"'"));
        }
    }
    }

    protected String chop(Node node) {
    return node.toString().trim();
    }

    public AlgebraTerm getTerm() {
    return this.term;
    }

    public void setContext(Program context) {
    this.prog = context;
    }

    public List getErrors() {
    if (this.errors.size() == 0) {
        return null;
    } else {
        return this.errors;
    }
    }

    public void checkErrors() throws ParserException {
    if (this.errors.size() != 0) {
        throw (ParserException)this.errors.get(0);
    }
    }

}
