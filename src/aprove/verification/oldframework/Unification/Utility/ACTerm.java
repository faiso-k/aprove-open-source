package aprove.verification.oldframework.Unification.Utility ;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** An AC-term.
 *
 *  @author  Stephan Falke
 *  @version $Id$
 */

public class ACTerm {

    private AlgebraTerm tt;
    private MultisetOfACTerms multiargs;
    private boolean hasMultiargs;
    private Vector<ACTerm> args;
    private boolean hasArgs;
    private Symbol symb;
    private Collection<SyntacticFunctionSymbol> Fac;

    /* constructros */
    private ACTerm(SyntacticFunctionSymbol f, Vector<ACTerm> args, Collection<SyntacticFunctionSymbol> Fac) {
    this.multiargs = null;
    this.args = args;
    this.hasArgs = true;
    this.hasMultiargs = false;

    this.Fac = Fac;
    this.symb = f;
    this.tt = this.constructTerm();
    }

    private ACTerm(SyntacticFunctionSymbol f, MultisetOfACTerms multiargs, Collection<SyntacticFunctionSymbol> Fac) {
    this.multiargs = multiargs;
    this.args = null;
    this.hasArgs = false;
    this.hasMultiargs = true;

    this.Fac = Fac;
    this.symb = f;
    this.tt = this.constructTerm();
    }

    private AlgebraTerm constructTerm() {
    if(this.symb instanceof VariableSymbol) {
        return AlgebraVariable.create((VariableSymbol)this.symb);
    }
    if(this.hasArgs) {
        Vector<AlgebraTerm> newArgs = new Vector<AlgebraTerm>();
        Iterator i = this.args.iterator();
        while(i.hasNext()) {
        newArgs.add(((ACTerm)i.next()).toTerm());
        }
        return AlgebraFunctionApplication.create((SyntacticFunctionSymbol)this.symb, newArgs);
    }
    else {
        Vector<AlgebraTerm> newArgs = new Vector<AlgebraTerm>();
        Enumeration e = this.multiargs.elements();
        while(e.hasMoreElements()) {
            ACTerm s = (ACTerm)e.nextElement();
        AlgebraTerm ss = s.toTerm();
        int n = this.multiargs.numberOfOccurences(s);
        for(int i=0; i<n; i++) {
            newArgs.add(ss);
        }
        }
        /* deflatten */
        /* newArgs has >= arity elements */
        return this.deflatten(newArgs);
    }
    }

    private AlgebraTerm deflatten(Vector<AlgebraTerm> args) {
    Vector<AlgebraTerm> resArgs = new Vector<AlgebraTerm>();
    int n = ((SyntacticFunctionSymbol)this.symb).getArity();
    if(args.size()==n) {
        for(int i=0; i<n; i++) {
            resArgs.add(args.elementAt(i));
        }
    }
    else {
        for(int i=0; i<n-1; i++) {
            resArgs.add(args.elementAt(i));
            args.removeElementAt(i);
        }
        resArgs.add(this.deflatten(args));
    }
    return AlgebraFunctionApplication.create((SyntacticFunctionSymbol)this.symb, resArgs);
    }

    private ACTerm(AlgebraTerm t, Collection<SyntacticFunctionSymbol> Fac) {
    this.multiargs = null;
    this.args = null;
    this.hasArgs = false;
    this.hasMultiargs = false;

    this.symb = t.getSymbol();
    this.tt = t.deepcopy();
    this.Fac = Fac;

    if(t.isVariable()) {
        return;
    }
    else {
        boolean isAC = Fac.contains(this.symb);
        if(isAC) {
        this.hasMultiargs = true;
            this.multiargs = MultisetOfACTerms.create();
            Iterator i = t.getArguments().iterator();
            while(i.hasNext()) {
            ACTerm s = ACTerm.create((AlgebraTerm)i.next(), Fac);
            if(s.symb.equals(this.symb)) {
            this.multiargs = this.multiargs.union(s.multiargs);
            }
            else {
                this.multiargs.add(s);
            }
            }
        }
        else {
        this.hasArgs = true;
        this.args = new Vector<ACTerm>();
            Iterator i = t.getArguments().iterator();
            while(i.hasNext()) {
            this.args.add(ACTerm.create((AlgebraTerm)i.next(), Fac));
            }
        }
    }
    }

    /** Returns a new instance of <code>ACTerm</code>.
     * @param t   the term that's to be transformed into an ACTerm
     * @param Fac   the AC symbols
     */
    public static ACTerm create(AlgebraTerm t, Collection<SyntacticFunctionSymbol> Fac) {
    return new ACTerm(t, Fac);
    }

    /** Returns a new instance of <code>ACTerm</code>.
     * @param f     the head function symbol
     * @param args  the arguments
     * @param Fac   the AC symbols
     */
    public static ACTerm create(SyntacticFunctionSymbol f, Vector<ACTerm> args, Collection<SyntacticFunctionSymbol> Fac) {
    return new ACTerm(f, args, Fac);
    }

    /** Returns a new instance of <code>ACTerm</code>.
     * @param f     the head function symbol
     * @param multiargs  the arguments
     * @param Fac   the AC symbols
     */
    public static ACTerm create(SyntacticFunctionSymbol f, MultisetOfACTerms multiargs, Collection<SyntacticFunctionSymbol> Fac) {
    if(multiargs.realSize()==1) {
        return ((ACTerm)multiargs.elements().nextElement()).deepcopy();
    }
    else {
        return new ACTerm(f, multiargs, Fac);
    }
    }

    public Sort getSort() {
    return this.symb.getSort();
    }

    public Collection<SyntacticFunctionSymbol> getFac() {
    return this.Fac;
    }

    public boolean isVariable() {
    return (this.symb instanceof VariableSymbol);
    }

    public boolean isConstant() {
    if(!(this.symb instanceof SyntacticFunctionSymbol)) {
        return false;
    }
    else {
        return ((SyntacticFunctionSymbol)this.symb).isConstant();
    }
    }

    public Symbol getSymbol() {
    return this.symb;
    }

    public ACTerm apply(VarAbstraction sub) {
    ACTerm res = this.deepcopy();

    Enumeration e = null;
    if(this.hasArgs) {
        e = this.args.elements();
        res.args = new Vector<ACTerm>();
    }
    else if(this.hasMultiargs) {
        e = this.multiargs.elements();
        res.multiargs = MultisetOfACTerms.create();
    }

    if(e!=null) {
        while(e.hasMoreElements()) {
        ACTerm cand = (ACTerm)e.nextElement();
        AlgebraVariable var = sub.get(cand);
        if(var!=null) {
            ACTerm vart = ACTerm.create(var, this.Fac);
            if(this.hasArgs) {
            res.args.add(vart);
            }
            else {
            res.multiargs.add(vart, this.multiargs.numberOfOccurences(cand));
            }
        }
        else {
            if(this.hasArgs) {
            res.args.add(cand);
            }
            else {
            res.multiargs.add(cand, this.multiargs.numberOfOccurences(cand));
            }
        }
        }
    }

    return res;
    }

    /** Returns the length of this AC-term.
     */
    public int length() {
    int res = 1;
    if(this.isVariable() || this.isConstant()) {
        return res;
    }
    if(this.hasArgs) {
        Enumeration e = this.args.elements();
        while(e.hasMoreElements()) {
        res += ((ACTerm)e.nextElement()).length();
        }
    }
    else {
        Enumeration e = this.multiargs.elements();
        while(e.hasMoreElements()) {
        ACTerm t = (ACTerm)e.nextElement();
        res += t.length() * this.multiargs.numberOfOccurences(t);
        }
    }
    return res;
    }

    /** Returns the alien subterms.
     */
    public Set<ACTerm> getAliens() {
    Set<ACTerm> res = new HashSet<ACTerm>();

    Enumeration e = null;
    if(this.hasArgs) {
        /* free symbol */
        e = this.args.elements();
        while(e.hasMoreElements()) {
        res.addAll(this.collectAliens((ACTerm)e.nextElement()));
        }
    }
    else if(this.hasMultiargs) {
        /* AC, i.e. get all immediate aliens */
        e = this.multiargs.elements();
        while(e.hasMoreElements()) {
        ACTerm cand = (ACTerm)e.nextElement();
        if(!cand.isVariable() && !cand.isConstant()) {
            /* it's an alien! */
            res.add(cand);
        }
        }
    }

    return res;
    }

    private Set<ACTerm> collectAliens(ACTerm t) {
    Set<ACTerm> res = new HashSet<ACTerm>();

    if(!t.isVariable() && !t.isConstant()) {
        if(this.Fac.contains(t.getSymbol())) {
        /* alien! */
        res.add(t);
        }
        else {
        /* descend into subterms */
        Enumeration e = t.elements();
        while(e.hasMoreElements()) {
            res.addAll(this.collectAliens((ACTerm)e.nextElement()));
        }
        }
    }

    return res;
    }

    /** Returns the set of variables that are immediate arguments of this AC-term and occur exactly once in the
     * AC-term.
     */
    public Set<AlgebraVariable> getLinearImmediateVars() {
    Set<AlgebraVariable> res = new HashSet<AlgebraVariable>();
    if(this.isVariable()) {
        res.add((AlgebraVariable) this.tt);
    }
    if(this.isVariable() || this.isConstant()) {
        return res;
    }

    Enumeration e;
    if(this.hasArgs) {
        e = this.args.elements();
    }
    else {
        e = this.multiargs.elements();
    }
    while(e.hasMoreElements()) {
        ACTerm arg = (ACTerm)e.nextElement();
        if(arg.isVariable() && this.tt.getNumberOfVarOcc((AlgebraVariable)arg.tt)==1) {
        res.add((AlgebraVariable) arg.tt);
        }
    }
    return res;
    }


    /** Returns a multiset of the variables occuring in this AC-term.
     */
    public MultisetOfACTerms getVars() {
    MultisetOfACTerms res = MultisetOfACTerms.create();

    if(this.isVariable()) {
        res.add(this);
    }
    if(this.isVariable() || this.isConstant()) {
        return res;
    }

    if(this.hasArgs) {
        Enumeration e = this.args.elements();
        while(e.hasMoreElements()) {
        res = res.union(((ACTerm)e.nextElement()).getVars());
        }
    }
    else {
        Enumeration e = this.multiargs.elements();
        while(e.hasMoreElements()) {
        ACTerm t = (ACTerm)e.nextElement();
        MultisetOfACTerms tmp = t.getVars();
        if(!tmp.isEmpty()) {
            for(int i=0; i<this.multiargs.numberOfOccurences(t); i++) {
            res = res.union(tmp);
            }
        }
        }
    }

    return res;
    }


    public boolean hasArgs() {
    return this.hasArgs;
    }

    public List<ACTerm> getArgs() {
    return this.args;
    }

    public boolean hasMultiArgs() {
    return this.hasMultiargs;
    }

    public MultisetOfACTerms getMultiargs() {
    return this.multiargs;
    }


    @Override
    public boolean equals(Object o) {
        ACTerm other;
    try {
        other = (ACTerm)o;
    }
    catch(ClassCastException e) {
        return false;
    }
    boolean res = this.symb.equals(other.symb);
    if(this.tt.isVariable() || other.tt.isVariable()) {
        return res;
    }
    if(res && (((SyntacticFunctionSymbol)this.symb).getArity()==0) ) {
        return res;
    }
    if(res==true) {
        if(this.hasMultiargs && other.hasMultiargs) {
            res = this.multiargs.equals(other.multiargs);
        }
        else if(this.hasArgs && other.hasArgs) {
        Iterator i1;
        Iterator i2;
            i1 = this.args.iterator();
            i2 = other.args.iterator();
            ACTerm s;
            ACTerm t;
            while(i1.hasNext() && res==true) {
            s = (ACTerm)i1.next();
            t = (ACTerm)i2.next();
                res = s.equals(t);
            }
        }
        else if(this.hasArgs || this.hasMultiargs) {
        /* one term has multiargs, the other one args */
        res = false;
        }
    }

    return res;
    }

    /** Returns a string representation of this multiset.
     */
    @Override
    public String toString() {
    StringBuffer res = new StringBuffer(this.symb.getName());

    Vector argStrings = null;
    if(this.multiargs != null) {
        argStrings = new Vector();
        Enumeration e = this.elements();
        while(e.hasMoreElements()) {
        ACTerm t = (ACTerm)e.nextElement();
        String ts = t.toString();
        for(int i=0; i<this.multiargs.numberOfOccurences(t); i++) {
            argStrings.add(ts);
        }
        }
    }
    if(this.args != null) {
        argStrings = new Vector();
        Enumeration e = this.elements();
        while(e.hasMoreElements()) {
        argStrings.add(e.nextElement().toString());
        }
    }
    if(!this.isConstant() && argStrings != null) {
        res.append("(");
        Iterator i = argStrings.iterator();
        while(i.hasNext()) {
        res.append(i.next().toString());
        if(i.hasNext()) {
            res.append(", ");
        }
        }
        res.append(")");
    }

    return res.toString();
    }

    /** Returns a term representation of this multiterm.
     */
    public AlgebraTerm toTerm() {
    return this.tt;
    }

    /** Returns a deep copy of this multiterm.
     */
    public ACTerm deepcopy() {
    return new ACTerm(this.toTerm(), this.Fac);
    }

    public Enumeration elements() {
    if(this.hasArgs) {
        return this.args.elements();
    }
    else if(this.hasMultiargs) {
        return this.multiargs.elements();
    }
    else {
        return null;
    }
    }

    private String toHashString() {
    StringBuffer res = new StringBuffer(this.symb.getName());
    if(!this.isVariable() && !this.isConstant()) {
        if(this.multiargs != null) {
            res.append(this.multiargs.toString());
        }
        if(this.args != null) {
            res = res.append(this.args.toString());
        }
    }
    return res.toString();
    }

    @Override
    public int hashCode() {
    return this.toHashString().hashCode();
    }

    public ACnCTerm toACnCTerm(Set<SyntacticFunctionSymbol> cs) {
    return ACnCTerm.create(this.tt, this.Fac, cs);
    }
}
