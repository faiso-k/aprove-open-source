package aprove.verification.oldframework.Algebra.Orders.Utility ;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Implementation of a multiterm, i.e. a term consisting of a root symbol
 * and a multiset of multiterms or a list of multiterms that represent the
 * arguments of the term. The multiterm is flattened w.r.t. AC symbols.
 *
 *  @author  Stephan Falke
 *  @version $Id$
 */

public class FlattenedMultiterm {
    private AlgebraTerm tt;
    private Symbol symb;
    private MultisetOfFlattenedMultiterms multiargs;
    private boolean hasMultiargs;
    private Vector<FlattenedMultiterm> args;
    private boolean hasArgs;
    private StatusMap map;
    private boolean isAC;

    /* constructros */

    private FlattenedMultiterm(AlgebraTerm t, StatusMap map) {
    this.tt = t.deepcopy();
    this.symb = this.tt.getSymbol();
    this.multiargs = null;
    this.args = null;
    this.map = map.deepcopy();

    this.hasArgs = false;
    this.hasMultiargs = false;
    if(this.tt.getArguments() != null) {
        this.isAC = map.hasFlatStatus(this.symb.getName());
        if(map.hasMultisetStatus(this.symb.getName()) || this.isAC) {
        /* the symbol has at least multiset status */
        this.hasMultiargs = true;
        this.hasArgs = false;
            this.multiargs = MultisetOfFlattenedMultiterms.create();
            Iterator i = this.tt.getArguments().iterator();
            while(i.hasNext()) {
            FlattenedMultiterm s = FlattenedMultiterm.create((AlgebraTerm)i.next(), map);
            if(this.isAC && s.symb.equals(this.symb)) {
            this.multiargs = this.multiargs.union(s.multiargs);
            }
            else {
                this.multiargs.add(s);
            }
            }
        }
        else {
        /* the symbol has either permutation status or no status */
        this.hasArgs = true;
        this.hasMultiargs = false;
        this.args = new Vector<FlattenedMultiterm>();
            Iterator i = this.tt.getArguments().iterator();
            while(i.hasNext()) {
            this.args.add(FlattenedMultiterm.create((AlgebraTerm)i.next(), map));
            }
        }
    }
    }

    /** Returns a new instance of <code>FlattenedMultiterm</code>, giving multiset or AC
     * status to those symbols having it according to a status map.
     * @param t   the term that's to be transformed into a multiterm
     * @param map the status map to be used for the transformation
     */
    public static FlattenedMultiterm create(AlgebraTerm t, StatusMap map) {
    return new FlattenedMultiterm(t, map);
    }

    /** The set of terms embedded in this Multiterm through an argument
     * headed by a non-big symbol w.r.t. the precedence if this multiterm is
     * an AC multiterm.
     */
    public Set<FlattenedMultiterm> embNoBig(Poset p) {
    if((this.symb instanceof VariableSymbol) || !this.map.hasFlatStatus(this.symb.getName())) {
        return null;
    }

    Set<FlattenedMultiterm> res = new HashSet<FlattenedMultiterm>();

    /* iterate on the immediate subterms */
    Enumeration e = this.multiargs.elements();
    while(e.hasMoreElements()) {
        FlattenedMultiterm s = (FlattenedMultiterm)e.nextElement();
        if(!(s.symb instanceof VariableSymbol)) {
        SyntacticFunctionSymbol h = (SyntacticFunctionSymbol)s.symb;
        /* no big? */
        if(!p.isGreater(h.getName(), this.symb.getName())) {
                /* iterate on the arguments of the subterm */
            Enumeration ee;
            if(s.hasArgs) {
            ee = s.args.elements();
            }
            else {
            ee = s.multiargs.elements();
            }
            while(ee.hasMoreElements()) {
            FlattenedMultiterm v = (FlattenedMultiterm)ee.nextElement();
            FlattenedMultiterm elem = this.deepcopy();
            elem.multiargs.remove(s);
            /* construct new term */
            if(v.symb instanceof VariableSymbol) {
                elem.multiargs.add(v);
            }
            else {
                SyntacticFunctionSymbol vhead = (SyntacticFunctionSymbol)v.symb;
                if(vhead.equals(this.symb)) {
                elem.multiargs = elem.multiargs.union(v.multiargs);
                }
                else {
                elem.multiargs.add(v);
                }
            }
            res.add(elem);
            }
        }
        }
    }
    return res;
    }

    /** The multiset of arguments of this multiterm headed
     * by a symbol not smaller than the root symbol of this multiterm
     * w.r.t. the precedence if this multiterm is an AC multiterm.
     */
    public MultisetOfFlattenedMultiterms noSmallHead(Poset p) {
    if((this.symb instanceof VariableSymbol) || !this.map.hasFlatStatus(this.symb.getName())) {
        return null;
    }

    MultisetOfFlattenedMultiterms res = MultisetOfFlattenedMultiterms.create();

    /* iterate on the immediate subterms */
    Enumeration e = this.multiargs.elements();
    while(e.hasMoreElements()) {
        FlattenedMultiterm s = (FlattenedMultiterm)e.nextElement();
        if(s.symb instanceof VariableSymbol) {
        res.add(s, this.multiargs.numberOfOccurences(s));
        }
        else {
        SyntacticFunctionSymbol shead = (SyntacticFunctionSymbol)s.symb;
        /* not smaller? */
        if(!p.isGreater(this.symb.getName(), shead.getName())) {
            res.add(s, this.multiargs.numberOfOccurences(s));
        }
        }
    }
    return res;
    }

    /** The multiset of arguments of this multiterm headed
     * by a symbol bigger than the root symbol of this multiterm
     * w.r.t. the precedence if this multiterm is an AC multiterm.
     */
    public MultisetOfFlattenedMultiterms bigHead(Poset p) {
    if((this.symb instanceof VariableSymbol) || !this.map.hasFlatStatus(this.symb.getName())) {
        return null;
    }

    MultisetOfFlattenedMultiterms res = MultisetOfFlattenedMultiterms.create();

    /* iterate on the immediate subterms */
    Enumeration e = this.multiargs.elements();
    while(e.hasMoreElements()) {
        FlattenedMultiterm s = (FlattenedMultiterm)e.nextElement();
        if(!(s.symb instanceof VariableSymbol)) {
        SyntacticFunctionSymbol shead = (SyntacticFunctionSymbol)s.symb;
        /* bigger? */
        if(p.isGreater(shead.getName(), this.symb.getName())) {
            res.add(s, this.multiargs.numberOfOccurences(s));
        }
        }
    }
    return res;
    }


    /** Returns <code>true</code> if this multiterm and the multiterm
     * <code>o</code> are equal, returns <code>false</code> otherwise.
     * If this multiterm was created with a qoset <code>q</code>, the
     * test is for quasi-equality.
     */
    @Override
    public boolean equals(Object o) {
        FlattenedMultiterm other;
    try {
        other = (FlattenedMultiterm)o;
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
            FlattenedMultiterm s;
            FlattenedMultiterm t;
            while(i1.hasNext() && res==true) {
            s = (FlattenedMultiterm)i1.next();
            t = (FlattenedMultiterm)i2.next();
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
    if(this.multiargs != null) {
        res.append(this.multiargs.toString());
    }
    if(this.args != null) {
        res.append(this.args.toString());
    }
    return res.toString();
    }

    /** Returns a term representation of this multiterm.
     */
    public AlgebraTerm toTerm() {
    if(this.symb instanceof VariableSymbol) {
        return AlgebraVariable.create((VariableSymbol)this.symb);
    }
    String symbName = this.symb.getName();
    if(this.hasArgs) {
        Vector<AlgebraTerm> newArgs = new Vector<AlgebraTerm>();
        Iterator i = this.args.iterator();
        while(i.hasNext()) {
        newArgs.add(((FlattenedMultiterm)i.next()).toTerm());
        }
        return AlgebraFunctionApplication.create((SyntacticFunctionSymbol)this.symb, newArgs);
    }
    if(this.map.hasMultisetStatus(symbName)) {
        Vector<AlgebraTerm> newArgs = new Vector<AlgebraTerm>();
        Enumeration e = this.multiargs.elements();
        while(e.hasMoreElements()) {
        FlattenedMultiterm s = (FlattenedMultiterm)e.nextElement();
        AlgebraTerm ss = s.toTerm();
        int n = this.multiargs.numberOfOccurences(s);
        for(int i=0; i<n; i++) {
            newArgs.add(ss);
        }
        }
        return AlgebraFunctionApplication.create((SyntacticFunctionSymbol)this.symb, newArgs);
    }
    if(this.map.hasFlatStatus(symbName)) {
        Vector<AlgebraTerm> newArgs = new Vector<AlgebraTerm>();
        Enumeration e = this.multiargs.elements();
        while(e.hasMoreElements()) {
        FlattenedMultiterm s = (FlattenedMultiterm)e.nextElement();
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
    return null;
    }

    private AlgebraTerm deflatten(Vector<AlgebraTerm> args) {
    Vector<AlgebraTerm> resArgs = new Vector<AlgebraTerm>();
    int n = ((SyntacticFunctionSymbol)this.symb).getArity();
    if(args.size()==n) {
        for(int i=0; i<n; i++) {
            resArgs.add((AlgebraTerm)args.elementAt(i));
        }
    }
    else {
        for(int i=0; i<n-1; i++) {
            resArgs.add((AlgebraTerm)args.elementAt(i));
            args.removeElementAt(i);
        }
        resArgs.add(this.deflatten(args));
    }
    return AlgebraFunctionApplication.create((SyntacticFunctionSymbol)this.symb, resArgs);
    }

    /** Returns a deep copy of this multiterm.
     */
    public FlattenedMultiterm deepcopy() {
    return new FlattenedMultiterm(this.toTerm(), this.map);
    }

    /** Returns the multiarguments of this multiterms if the head symbol
     * has multiset status or AC status.
     */
    public MultisetOfFlattenedMultiterms getMultiArguments() {
    return this.multiargs;
    }

    @Override
    public int hashCode() {
    return this.toString().hashCode();
    }

    public Symbol getSymbol() {
    return this.symb;
    }

    public boolean isVariable() {
    return this.tt.isVariable();
    }

}
