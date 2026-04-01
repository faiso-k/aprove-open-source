package aprove.verification.oldframework.Unification.Utility ;

import java.util.*;

import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** An AC-and-C-term.
 *
 *  @author  Stephan Falke
 *  @version $Id$
 */

public class ACnCTerm {

    private AlgebraTerm tt;
    private MultisetOfACnCTerms multiargs;
    private boolean hasMultiargs;
    private Vector<ACnCTerm> args;
    private boolean hasArgs;
    private Symbol symb;
    private Collection<SyntacticFunctionSymbol> Fac;
    private Collection<SyntacticFunctionSymbol> Fc;

    /* constructros */
    private ACnCTerm(SyntacticFunctionSymbol f, Vector<ACnCTerm> args, Collection<SyntacticFunctionSymbol> Fac, Collection<SyntacticFunctionSymbol> Fc) {
    this.multiargs = null;
    this.args = args;
    this.hasArgs = true;
    this.hasMultiargs = false;

    this.Fac = Fac;
    this.Fc = Fc;
    this.symb = f;
    this.tt = this.constructTerm();
    }

    private ACnCTerm(SyntacticFunctionSymbol f, MultisetOfACnCTerms multiargs, Collection<SyntacticFunctionSymbol> Fac, Collection<SyntacticFunctionSymbol> Fc) {
    this.multiargs = multiargs;
    this.args = null;
    this.hasArgs = false;
    this.hasMultiargs = true;

    this.Fac = Fac;
    this.Fc = Fc;
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
        newArgs.add(((ACnCTerm)i.next()).toTerm());
        }
        return AlgebraFunctionApplication.create((SyntacticFunctionSymbol)this.symb, newArgs);
    }
    else {
        Vector<AlgebraTerm> newArgs = new Vector<AlgebraTerm>();
        Enumeration e = this.multiargs.elements();
        while(e.hasMoreElements()) {
            ACnCTerm s = (ACnCTerm)e.nextElement();
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

    private ACnCTerm(AlgebraTerm t, Collection<SyntacticFunctionSymbol> Fac, Collection<SyntacticFunctionSymbol> Fc) {
    this.multiargs = null;
    this.args = null;
    this.hasArgs = false;
    this.hasMultiargs = false;

    this.symb = t.getSymbol();
    this.tt = t.deepcopy();
    this.Fac = Fac;
    this.Fc = Fc;

    if(t.isVariable()) {
        return;
    }
    else {
        boolean isAC = Fac.contains(this.symb);
        boolean isC = Fc.contains(this.symb);
        if(isAC || isC) {
        this.hasMultiargs = true;
            this.multiargs = MultisetOfACnCTerms.create();
            Iterator i = t.getArguments().iterator();
            while(i.hasNext()) {
            ACnCTerm s = ACnCTerm.create((AlgebraTerm)i.next(), Fac, Fc);
            if(s.symb.equals(this.symb) && isAC) {
            /* flatten */
            this.multiargs = this.multiargs.union(s.multiargs);
            }
            else {
                this.multiargs.add(s);
            }
            }
        }
        else {
        this.hasArgs = true;
        this.args = new Vector<ACnCTerm>();
            Iterator i = t.getArguments().iterator();
            while(i.hasNext()) {
            this.args.add(ACnCTerm.create((AlgebraTerm)i.next(), Fac, Fc));
            }
        }
    }
    }

    /** Returns a new instance of <code>ACnCTerm</code>.
     * @param t   the term that's to be transformed into an ACnCTerm
     * @param Fac   the AC symbols
     * @param Fc   the C symbols
     */
    public static ACnCTerm create(AlgebraTerm t, Collection<SyntacticFunctionSymbol> Fac, Collection<SyntacticFunctionSymbol> Fc) {
    return new ACnCTerm(t, Fac, Fc);
    }

    /** Returns a new instance of <code>ACnCTerm</code>.
     * @param f     the head function symbol
     * @param args  the arguments
     * @param Fac   the AC symbols
     * @param Fc   the C symbols
     */
    public static ACnCTerm create(SyntacticFunctionSymbol f, Vector<ACnCTerm> args, Collection<SyntacticFunctionSymbol> Fac, Collection<SyntacticFunctionSymbol> Fc) {
    return new ACnCTerm(f, args, Fac, Fc);
    }

    /** Returns a new instance of <code>ACnCTerm</code>.
     * @param f     the head function symbol
     * @param multiargs  the arguments
     * @param Fac   the AC symbols
     * @param Fc   the C symbols
     */
    public static ACnCTerm create(SyntacticFunctionSymbol f, MultisetOfACnCTerms multiargs, Collection<SyntacticFunctionSymbol> Fac, Collection<SyntacticFunctionSymbol> Fc) {
    if(multiargs.realSize()==1) {
        return ((ACnCTerm)multiargs.elements().nextElement()).deepcopy();
    }
    else {
        return new ACnCTerm(f, multiargs, Fac, Fc);
    }
    }

    public Sort getSort() {
    return this.symb.getSort();
    }

    public Collection<SyntacticFunctionSymbol> getFac() {
    return this.Fac;
    }

    public Collection<SyntacticFunctionSymbol> getFc() {
    return this.Fc;
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

    public ACnCTerm apply(ExtVarAbstraction sub) {
    ACnCTerm res = this.deepcopy();

    Enumeration e = null;
    if(this.hasArgs) {
        e = this.args.elements();
        res.args = new Vector<ACnCTerm>();
    }
    else if(this.hasMultiargs) {
        e = this.multiargs.elements();
        res.multiargs = MultisetOfACnCTerms.create();
    }

    if(e!=null) {
        while(e.hasMoreElements()) {
        ACnCTerm cand = (ACnCTerm)e.nextElement();
        AlgebraVariable var = sub.get(cand);
        if(var!=null) {
            ACnCTerm vart = ACnCTerm.create(var, this.Fac, this.Fc);
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

    /** Returns the length of this AC-and-C-term.
     */
    public int length() {
    int res = 1;
    if(this.isVariable() || this.isConstant()) {
        return res;
    }
    if(this.hasArgs) {
        Enumeration e = this.args.elements();
        while(e.hasMoreElements()) {
        res += ((ACnCTerm)e.nextElement()).length();
        }
    }
    else {
        Enumeration e = this.multiargs.elements();
        while(e.hasMoreElements()) {
        ACnCTerm t = (ACnCTerm)e.nextElement();
        res += t.length() * this.multiargs.numberOfOccurences(t);
        }
    }
    return res;
    }

    /** Returns the alien subterms.
     */
    public Set<ACnCTerm> getAliens() {
    Set<ACnCTerm> res = new HashSet<ACnCTerm>();

    Enumeration e = null;
    if(this.hasArgs) {
        /* free symbol */
        e = this.args.elements();
        while(e.hasMoreElements()) {
        res.addAll(this.collectAliens((ACnCTerm)e.nextElement()));
        }
    }
    else if(this.hasMultiargs) {
        /* AC or C, i.e. get all immediate subterms */
        e = this.multiargs.elements();
        while(e.hasMoreElements()) {
        ACnCTerm cand = (ACnCTerm)e.nextElement();
        if(!cand.isVariable() && !cand.isConstant()) {
            /* it's an alien! */
            res.add(cand);
        }
        }
    }

    return res;
    }

    private Set<ACnCTerm> collectAliens(ACnCTerm t) {
    Set<ACnCTerm> res = new HashSet<ACnCTerm>();

    if(!t.isVariable() && !t.isConstant()) {
        if(this.Fac.contains(t.getSymbol())
           || this.Fc.contains(t.getSymbol())) {
        /* alien! */
        res.add(t);
        }
        else {
        /* descend into subterms */
        Enumeration e = t.elements();
        while(e.hasMoreElements()) {
            res.addAll(this.collectAliens((ACnCTerm)e.nextElement()));
        }
        }
    }

    return res;
    }

    /** Returns a multiset of the variables occuring in this AC-term.
     */
    public MultisetOfACnCTerms getVars() {
    MultisetOfACnCTerms res = MultisetOfACnCTerms.create();

    if(this.isVariable()) {
        res.add(this);
    }
    if(this.isVariable() || this.isConstant()) {
        return res;
    }

    if(this.hasArgs) {
        Enumeration e = this.args.elements();
        while(e.hasMoreElements()) {
        res = res.union(((ACnCTerm)e.nextElement()).getVars());
        }
    }
    else {
        Enumeration e = this.multiargs.elements();
        while(e.hasMoreElements()) {
        ACnCTerm t = (ACnCTerm)e.nextElement();
        MultisetOfACnCTerms tmp = t.getVars();
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

    public List<ACnCTerm> getArgs() {
    return this.args;
    }

    public boolean hasMultiArgs() {
    return this.hasMultiargs;
    }

    public MultisetOfACnCTerms getMultiargs() {
    return this.multiargs;
    }

    public List<ACnCTerm> getArgVec() {
    List<ACnCTerm> res = new Vector<ACnCTerm>();
    if(this.hasArgs) {
        Enumeration e = this.args.elements();
        while(e.hasMoreElements()) {
        res.add((ACnCTerm)e.nextElement());
        }
    }
    else if(this.hasMultiargs) {
        Enumeration e = this.multiargs.elements();
        while(e.hasMoreElements()) {
        ACnCTerm t = (ACnCTerm)e.nextElement();
        int n = this.multiargs.numberOfOccurences(t);
        for(int i=0; i<n; i++) {
            res.add(t);
        }
        }
    }
    return res;
    }

    @Override
    public boolean equals(Object o) {
        ACnCTerm other;
    try {
        other = (ACnCTerm)o;
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
            ACnCTerm s;
            ACnCTerm t;
            while(i1.hasNext() && res==true) {
            s = (ACnCTerm)i1.next();
            t = (ACnCTerm)i2.next();
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
        ACnCTerm t = (ACnCTerm)e.nextElement();
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
    public ACnCTerm deepcopy() {
    return new ACnCTerm(this.toTerm(), this.Fac, this.Fc);
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

    public ACTerm toACTerm() {
    return ACTerm.create(this.tt, this.Fac);
    }

    /** Returns the set of variables that are direct arguments of this ACnC-term and don't occur any deeper in this
     * ACnC-term.
     */
    public Set<AlgebraVariable> getJustDirectVars() {
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
        ACnCTerm arg = (ACnCTerm)e.nextElement();
        if(arg.isVariable() && this.tt.getNumberOfVarOcc((AlgebraVariable)arg.tt)==this.getNumberDirectVarOccs((AlgebraVariable)arg.tt)) {
        res.add((AlgebraVariable) arg.tt);
        }
    }
    return res;
    }

    private int getNumberDirectVarOccs(AlgebraVariable v) {
    if(this.tt.equals(v)) {
        return 1;
    }
    if(this.isVariable() || this.isConstant()) {
        return 0;
    }

    Enumeration e;
    int res = 0;
    if(this.hasArgs) {
        e = this.args.elements();
    }
    else {
        e = this.multiargs.elements();
    }
    while(e.hasMoreElements()) {
        ACnCTerm arg = (ACnCTerm)e.nextElement();
        if(arg.tt.equals(v)) {
        res++;
        }
    }
    return res;
    }

    /** Returns the set of normal subterms for innermost graph approximation with rencapAC.
     */
    public Set<ACnCTerm> getNormalSubs() {
    Set<ACnCTerm> res = new LinkedHashSet<ACnCTerm>();
    if(this.isVariable()) {
        res.add(this);
        return res;
    }
    if(this.Fac.contains(this.symb)) {
        Enumeration e = this.elements();
        Set<AlgebraVariable> nonnorm = this.getJustDirectVars();
        while(e.hasMoreElements()) {
        ACnCTerm arg = (ACnCTerm)e.nextElement();
        if(!arg.isVariable() || !nonnorm.contains(arg.tt)) {
            res.addAll(arg.getNormalSubsHelper());
        }
        }
    }
    else {
        res.add(this);
        Enumeration e = this.elements();
        while(e.hasMoreElements()) {
        ACnCTerm arg = (ACnCTerm)e.nextElement();
        res.addAll(arg.getNormalSubsHelper());
        }
    }
        return res;
    }

    private Set<ACnCTerm> getNormalSubsHelper() {
    Set<ACnCTerm> res = new LinkedHashSet<ACnCTerm>();
    if(this.isVariable()) {
        res.add(this);
        return res;
    }
    if(this.Fac.contains(this.symb)) {
        /* now this is the interesting case */
        List<ACnCTerm> args = this.multiargs.toList();
        int n = args.size();
        for (Sequence s : SequenceGenerator.create(n, 2)) {
        MultisetOfACnCTerms newargs = MultisetOfACnCTerms.create();
        for(int i=0; i<n; i++) {
            if(s.get(i)==1) {
            newargs.add(args.get(i));
            }
        }
        if(newargs.size()>1) {
            res.add(ACnCTerm.create((SyntacticFunctionSymbol)this.symb, newargs, this.Fac, this.Fc));
        }
        }
    }
    res.add(this);
    Enumeration e = this.elements();
    while(e.hasMoreElements()) {
        ACnCTerm arg = (ACnCTerm)e.nextElement();
        res.addAll(arg.getNormalSubsHelper());
    }
        return res;
    }

}
