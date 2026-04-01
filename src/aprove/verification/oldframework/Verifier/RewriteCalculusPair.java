package aprove.verification.oldframework.Verifier;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

public class RewriteCalculusPair {

    protected AlgebraTerm condition;
    protected List<AlgebraTerm> terms;
    protected int nrOfCaseAnalyses;

    protected RewriteCalculusPair(AlgebraTerm condition, List<AlgebraTerm> terms, int nrOfCaseAnalyses) {
    this.condition = condition;
    this.terms = terms;
    this.nrOfCaseAnalyses = nrOfCaseAnalyses;
    }

    public RewriteCalculusPair(AlgebraTerm condition, List<AlgebraTerm> terms) {
    this.condition = condition;
    this.terms = terms;
    this.nrOfCaseAnalyses = 0;
    }

    public RewriteCalculusPair(AlgebraTerm condition, AlgebraTerm term) {
    this.condition = condition;
    this.terms = new Vector<AlgebraTerm>();
    this.terms.add(term);
    }

    public AlgebraTerm getCondition() {
    return this.condition;
    }

    public void setCondition(AlgebraTerm condition) {
    this.condition = condition;
    }

    public List<AlgebraTerm> getTerms() {
    return this.terms;
    }

    public AlgebraTerm getTerm(int i) {
    return (AlgebraTerm)this.terms.get(i);
    }

    public void setTerms(List<AlgebraTerm> terms) {
    this.terms = terms;
    }

    public int getNrOfCaseAnalyses() {
    return this.nrOfCaseAnalyses;
    }

    public void setNrOfCaseAnalyses(int i) {
    this.nrOfCaseAnalyses = i;
    }

    public boolean isTrue() {
    Iterator it = this.terms.iterator();
    while (it.hasNext()) {
        AlgebraTerm t = (AlgebraTerm)it.next();
        if (!t.getSymbol().getName().equals("true")) {
        return false;
        }
    }
    return true;
    }

    public boolean conditionIsFalse() {
    return this.condition.getSymbol().getName().equals("false");
    }

    public RewriteCalculusPair deepcopy() {
    Vector<AlgebraTerm> newterms = new Vector<AlgebraTerm>();
    Iterator it = this.terms.iterator();
    while (it.hasNext()) {
        newterms.add(((AlgebraTerm)it.next()).deepcopy());
    }
    return new RewriteCalculusPair(this.condition.deepcopy(), newterms, this.nrOfCaseAnalyses);
    }

    @Override
    public String toString() {
    StringBuffer out = new StringBuffer("<"+RewriteCalculusPair.termToString(this.condition)+", {");
    Iterator it = this.terms.iterator();
    while (it.hasNext()) {
        AlgebraTerm t = (AlgebraTerm)it.next();
        out.append(RewriteCalculusPair.termToString(t));
        if (it.hasNext()) {
        out.append(", ");
        }
    }
    out.append("}> ("+this.nrOfCaseAnalyses+")");
    return out.toString();
    }

    /* Just to help debugging */
    public static String termToString(AlgebraTerm term) {
    if (term.isVariable()) {
        return term.toString();
    }
    SyntacticFunctionSymbol f = (SyntacticFunctionSymbol)term.getSymbol();
    StringBuffer out = new StringBuffer(f.getName());
    Hashtable label = (Hashtable)term.getAttribute("label");
    if (label != null) {
        out.append(label.toString());
    }
    out.append("(");
    Iterator it = term.getArguments().iterator();
    while (it.hasNext()) {
        out.append(RewriteCalculusPair.termToString((AlgebraTerm)it.next()));
        if (it.hasNext()) {
        out.append(", ");
        }
    }
    out.append(")");
    return out.toString();
    }

    /** Labels the terms and the condition with an empty hashtable.
     */
    public void label() {
    this.labelTerm(this.condition, new Hashtable());
    Iterator it = this.terms.iterator();
    while (it.hasNext()) {
        AlgebraTerm t = (AlgebraTerm)it.next();
        t.labelTerm(new Hashtable());
    }
    }

    /** Labels a given term with a given label. E.g. every subterm whose
     *  root-symbol is a defining function-symbol gets the attribute
     *  "label" with the value given as label.
     *  @param term The term that is to be labeled.
     *  @param label The label.
     */
    private void labelTerm(AlgebraTerm term, Hashtable label) {
    if (term.isVariable()) {
        return;
    }
    SyntacticFunctionSymbol f = (SyntacticFunctionSymbol)term.getSymbol();
    if (f instanceof DefFunctionSymbol && !((DefFunctionSymbol)f).getTermination()) {
        term.setAttribute("label", new Hashtable(label));
    }
    Iterator it = term.getArguments().iterator();
    while (it.hasNext()) {
        this.labelTerm((AlgebraTerm)it.next(), label);
    }
    }

}
