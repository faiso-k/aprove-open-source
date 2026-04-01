package aprove.input.Programs.fp;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/**
 * A Class representing terms with conditions. This is needed to
 * translate functional programs into conditional trs.
 * A term is represented by a set of tuples. Each tuple has
 * three elements. The first is a list of trs-terms that have
 * to evaluate to true, the second ist a list of trs-terms
 * that have to evaluate to false, the third element is a
 * trs-term representing the actual term.
 * @author Christian Haselbach
 */

class CondTerm {

    /**
     * The set of tuples representing the term.
     */
    private Set<CondTermTuple> term;

    /**
     * Creates an empty term.
     */
    public CondTerm() {
    this.term = new HashSet<CondTermTuple>();
    }

    /**
     * Creates a term with one tuple.
     */
    private CondTerm(CondTermTuple v) {
    this.term = new HashSet<CondTermTuple>();
    this.term.add(v);
    }

    /**
     * Creates a term with a given tuple-set.
     */
    private CondTerm(Set<CondTermTuple> s) {
    this.term = s;
    }

    /**
     * Creates a term out of a trs-term (without conditions).
     */
    public static CondTerm create(AlgebraTerm x) {
    return new CondTerm(new CondTermTuple(x));
    }


    /**
     * Creates a term out of a three given terms representing an
     * if-construction.
     */
    public static CondTerm createIf(CondTerm co, CondTerm th, CondTerm el, Program prog) {
    Set nterm = new HashSet<CondTermTuple>();
    AlgebraTerm cotrue = AlgebraFunctionApplication.create((SyntacticFunctionSymbol)prog.getSymbol("true"));
    AlgebraTerm cofalse = AlgebraFunctionApplication.create((SyntacticFunctionSymbol)prog.getSymbol("false"));
    Iterator co_it = co.iterator();
    while (co_it.hasNext()) {
        CondTermTuple c = (CondTermTuple)co_it.next();
        Symbol sym = c.term.getSymbol();
        Iterator t_it = th.iterator();
        while (t_it.hasNext()) {
        CondTermTuple ct = ((CondTermTuple)t_it.next()).create_true(c, cotrue);
        nterm.add(ct);
        }
        t_it = el.iterator();
        while (t_it.hasNext()) {
        CondTermTuple ct = ((CondTermTuple)t_it.next()).create_false(c, cofalse);
        nterm.add(ct);
        }
    }
    return new CondTerm(nterm);
    }

    /**
     * Creates a term out of a function-symbol and a list of terms.
     * The length of the list has to be the arrity of the function.
     */
    public static CondTerm createApp(SyntacticFunctionSymbol f, CondTerm[] t) {
    int n = t.length;
    Set nterm = new HashSet<CondTermTuple>();
    Iterator it[] = new Iterator[n];
    CondTermTuple v[] = new CondTermTuple[n];
    int i, j;
    for (i=0; i<n; i++) {
        it[i] = t[i].iterator();
        if (!it[i].hasNext()) {
        return null;
        }
        v[i] = (CondTermTuple)it[i].next();
    }
    do {
        Vector<AlgebraTerm> params = new Vector<AlgebraTerm>();
        CondTermTuple nv = new CondTermTuple();
        for (i=0; i<n; i++) {
        nv.merge(v[i]);
        params.add(v[i].term);
        }
        if (f instanceof DefFunctionSymbol) {
        nv.set_term(DefFunctionApp.create((DefFunctionSymbol)f, params));
        }
        else {
        nv.set_term(ConstructorApp.create((ConstructorSymbol)f, params));
        }
        nterm.add(nv);
        i = n-1;
        while(i>=0 && !it[i].hasNext()) {
        it[i] = t[i].iterator();
        v[i] = (CondTermTuple)it[i].next();
        i--;
        }
        if (i>=0) {
            v[i] = (CondTermTuple)it[i].next();
        }
    } while(i>=0);
    return new CondTerm(nterm);
    }

    public static CondTerm createLet(CondTerm left, AlgebraTerm right, CondTerm term) {
    Set<CondTermTuple> newterm = new HashSet<CondTermTuple>();
    Iterator ct1_it = left.term.iterator();
    while (ct1_it.hasNext()) {
        CondTermTuple ctt1 = (CondTermTuple)ct1_it.next();
        Iterator ct2_it = term.term.iterator();
        while (ct2_it.hasNext()) {
        CondTermTuple ctt2 = (CondTermTuple)ct2_it.next();
        newterm.add(ctt2.create(right, ctt1));
        }
    }
    return new CondTerm(newterm);
    }

    /**
     * Adds the rules yielded by this term to a program.
     */
    public void addRulesToProg(Program prog, DefFunctionSymbol f, AlgebraTerm left) {
    Iterator it = this.term.iterator();
    while (it.hasNext()) {
        prog.addRule(f, ((CondTermTuple)it.next()).get_rule(left));
    }
    }

    /**
     * Returns the rules yielded by this term.
     */
    public LinkedHashSet<Rule> getRules(AlgebraTerm left) {
        LinkedHashSet<Rule> resultingRules = new LinkedHashSet<Rule>();
        Iterator it = this.term.iterator();
        while (it.hasNext()) {
            Rule rule = ((CondTermTuple)it.next()).get_rule(left);
            resultingRules.add(rule);
        }
        return resultingRules;
    }


    public Iterator<CondTermTuple> iterator() {
    return this.term.iterator();
    }

    public int size() {
        return this.term.size();
    }

    @Override
    public String toString() {
    StringBuffer str = new StringBuffer("{");
    Iterator it = this.term.iterator();
    while (it.hasNext()) {
        CondTermTuple ctt = (CondTermTuple)it.next();
        str.append(ctt.toString());
        if (it.hasNext()) {
            str.append(", ");
        }
    }
    return str.toString();
    }


    public CondTerm deepcopy() {
        CondTerm ctNew = new CondTerm();
        CondTermTuple cttNew = new CondTermTuple();
        for(CondTermTuple ctt : this.term) {
            for(Rule co : ctt.conds) {
                cttNew.conds.add(co.deepcopy());
            }
            cttNew.term = ctt.term.deepcopy();
            ctNew.term.add(cttNew);
        }
        return ctNew;
    }
}
