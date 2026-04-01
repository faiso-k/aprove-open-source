package aprove.verification.dpframework.Orders.Utility ;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/** Implementation of a multiterm, i.e. a term consisting of a root symbol
 * and a multiset of multiterms or a list of multiterms that represent the
 * arguments of the term. The multiterm is flattened w.r.t. AC symbols.
 *
 *  @author  Stephan Falke
 *  @version $Id$
 */

public class FlattenedMultiterm {
    private TRSTerm tt;
    private FunctionSymbol symb;
    private MultiSet<FlattenedMultiterm> multiargs;
    private boolean hasMultiargs;
    private ArrayList<FlattenedMultiterm> args;
    private boolean hasArgs;
    private StatusMap<FunctionSymbol> map;
    private boolean isAC;

    /* constructros */

    private FlattenedMultiterm(TRSTerm t, StatusMap<FunctionSymbol> map) {
        this.tt = t;
        if (this.tt.isVariable()) {
            this.symb = null;
        } else {
            this.symb = ((TRSFunctionApplication)this.tt).getRootSymbol();
        }
    this.multiargs = null;
    this.args = null;
    this.map = map.deepcopy();

    this.hasArgs = false;
    this.hasMultiargs = false;
    if(!this.tt.isVariable()) {
            TRSFunctionApplication ftt = (TRSFunctionApplication)this.tt;
        this.isAC = map.hasFlatStatus(this.symb);
        if(map.hasMultisetStatus(this.symb) || this.isAC) {
        /* the symbol has at least multiset status */
        this.hasMultiargs = true;
        this.hasArgs = false;
            this.multiargs = new HashMultiSet<FlattenedMultiterm>();
            for (TRSTerm arg : ftt.getArguments()) {
            FlattenedMultiterm s = FlattenedMultiterm.create(arg, map);
            if(s.symb == null && this.symb == null) {
                this.multiargs = this.multiargs.union(s.multiargs);
            }
            else if(s.symb != null && this.symb != null && this.isAC && s.symb.equals(this.symb)) {
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
        this.args = new ArrayList<FlattenedMultiterm>();
            for (TRSTerm arg : ftt.getArguments()) {
            this.args.add(FlattenedMultiterm.create(arg, map));
            }
        }
    }
    }

    /** Returns a new instance of <code>FlattenedMultiterm</code>, giving multiset or AC
     * status to those symbols having it according to a status map.
     * @param t   the term that's to be transformed into a multiterm
     * @param map the status map to be used for the transformation
     */
    public static FlattenedMultiterm create(TRSTerm t, StatusMap<FunctionSymbol> map) {
    return new FlattenedMultiterm(t, map);
    }

    /** The set of term> embedded in this Multiterm through an argument
     * headed by a non-big symbol w.r.t. the precedence if this multiterm is
     * an AC multiterm.
     */
    public Set<FlattenedMultiterm> embNoBig(Poset<FunctionSymbol> p) {
    if((this.symb == null) || !this.map.hasFlatStatus(this.symb)) {
        return null;
    }

    Set<FlattenedMultiterm> res = new HashSet<FlattenedMultiterm>();

    /* iterate on the immediate subterm> */
    Iterator<FlattenedMultiterm> e = this.multiargs.keySet().iterator();
    while(e.hasNext()) {
        FlattenedMultiterm s = e.next();
        if(!(s.symb == null)) {
        FunctionSymbol h = s.symb;
        /* no big? */
        if(!p.isGreater(h, this.symb)) {
                /* iterate on the arguments of the subterm */
            Iterator<FlattenedMultiterm> ee;
            if(s.hasArgs) {
            ee = s.args.iterator();
            }
            else {
            ee = s.multiargs.keySet().iterator();
            }
            while(ee.hasNext()) {
            FlattenedMultiterm v = ee.next();
            FlattenedMultiterm elem = this.deepcopy();
            elem.multiargs.removeOne(s);
            /* construct new term */
            if(v.symb == null) {
                elem.multiargs.add(v);
            }
            else {
                FunctionSymbol vhead = (FunctionSymbol)v.symb;
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
    public MultiSet<FlattenedMultiterm> noSmallHead(Poset<FunctionSymbol> p) {
    if((this.symb == null) || !this.map.hasFlatStatus(this.symb)) {
        return null;
    }

    MultiSet<FlattenedMultiterm> res = new HashMultiSet<FlattenedMultiterm>();

    /* iterate on the immediate subterm> */
    Iterator<FlattenedMultiterm> e = this.multiargs.keySet().iterator();
    while(e.hasNext()) {
        FlattenedMultiterm s = e.next();
        if(s.symb == null) {
        res.add(s, this.multiargs.frequency(s));
        }
        else {
        FunctionSymbol shead = s.symb;
        /* not smaller? */
        if(!p.isGreater(this.symb, shead)) {
            res.add(s, this.multiargs.frequency(s));
        }
        }
    }
    return res;
    }

    /** The multiset of arguments of this multiterm headed
     * by a symbol bigger than the root symbol of this multiterm
     * w.r.t. the precedence if this multiterm is an AC multiterm.
     */
    public MultiSet<FlattenedMultiterm> bigHead(Poset<FunctionSymbol> p) {
    if((this.symb == null) || !this.map.hasFlatStatus(this.symb)) {
        return null;
    }

    MultiSet<FlattenedMultiterm> res = new HashMultiSet<FlattenedMultiterm>();

    /* iterate on the immediate subterm> */
    Iterator<FlattenedMultiterm> e = this.multiargs.keySet().iterator();
    while(e.hasNext()) {
        FlattenedMultiterm s = e.next();
        if(!(s.symb == null)) {
        FunctionSymbol shead = s.symb;
        /* bigger? */
        if(p.isGreater(shead, this.symb)) {
            res.add(s, this.multiargs.frequency(s));
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
        if (this.symb == null || other.symb == null) {
            return this.tt.equals(other.tt);
        }
        boolean res = this.symb.equals(other.symb);
    if(res && (this.symb.getArity()==0) ) {
        return res;
    }
    if(res==true) {
        if(this.hasMultiargs && other.hasMultiargs) {
            res = this.multiargs.equals(other.multiargs);
        }
        else if(this.hasArgs && other.hasArgs) {
        Iterator<FlattenedMultiterm> i1;
        Iterator<FlattenedMultiterm> i2;
            i1 = this.args.iterator();
            i2 = other.args.iterator();
            FlattenedMultiterm s;
            FlattenedMultiterm t;
            while(i1.hasNext() && res==true) {
            s = i1.next();
            t = i2.next();
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
    StringBuffer res = new StringBuffer();
        if (this.tt.isVariable()) {
            res.append(((TRSVariable)this.tt).getName());
        } else {
            res.append(this.symb);
        }
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
    public TRSTerm toTerm() {
    if(this.symb == null) {
        return this.tt;
    }
    if(this.hasArgs) {
        ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
        Iterator<FlattenedMultiterm> i = this.args.iterator();
        while(i.hasNext()) {
        newArgs.add(i.next().toTerm());
        }
        return TRSTerm.createFunctionApplication(this.symb, ImmutableCreator.create(newArgs));
    }
    if(this.map.hasMultisetStatus(this.symb)) {
        ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
        Iterator<FlattenedMultiterm> e = this.multiargs.keySet().iterator();
        while(e.hasNext()) {
        FlattenedMultiterm s = e.next();
        TRSTerm ss = s.toTerm();
        int n = this.multiargs.frequency(s);
        for(int i=0; i<n; i++) {
            newArgs.add(ss);
        }
        }
        return TRSTerm.createFunctionApplication(this.symb, ImmutableCreator.create(newArgs));
    }
    if(this.map.hasFlatStatus(this.symb)) {
        ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
        Iterator<FlattenedMultiterm> e = this.multiargs.keySet().iterator();
        while(e.hasNext()) {
        FlattenedMultiterm s = e.next();
        TRSTerm ss = s.toTerm();
        int n = this.multiargs.frequency(s);
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

    private TRSTerm deflatten(ArrayList<TRSTerm> args) {
    ArrayList<TRSTerm> resArgs = new ArrayList<TRSTerm>();
    int n = ((FunctionSymbol)this.symb).getArity();
    if(args.size()==n) {
        for(int i=0; i<n; i++) {
            resArgs.add((TRSTerm)args.get(i));
        }
    }
    else {
        for(int i=0; i<n-1; i++) {
            resArgs.add((TRSTerm)args.get(i));
            args.remove(i);
        }
        resArgs.add(this.deflatten(args));
    }
    return TRSTerm.createFunctionApplication(this.symb, ImmutableCreator.create(resArgs));
    }

    /** Returns a deep copy of this multiterm.
     */
    public FlattenedMultiterm deepcopy() {
    return new FlattenedMultiterm(this.toTerm(), this.map);
    }

    /** Returns the multiarguments of this multiterm> if the head symbol
     * has multiset status or AC status.
     */
    public MultiSet<FlattenedMultiterm> getMultiArguments() {
    return this.multiargs;
    }

    @Override
    public int hashCode() {
    return this.toString().hashCode();
    }

    public FunctionSymbol getRootSymbol() {
    return this.symb;
    }

    public boolean isVariable() {
    return this.tt.isVariable();
    }

    public static MultiSet<TRSTerm> toTerm(MultiSet<FlattenedMultiterm> other) {
        MultiSet<TRSTerm> res = new HashMultiSet<TRSTerm>();
        for (Map.Entry<FlattenedMultiterm,Integer> entry : other.entrySet()) {
            res.add(entry.getKey().toTerm(), entry.getValue());
        }
        return res;
    }

}
