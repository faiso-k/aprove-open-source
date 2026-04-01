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

public class FlattenedQuasiMultiterm {
    private TRSTerm tt;
    private FunctionSymbol symb;
    private MultiSet<FlattenedQuasiMultiterm> multiargs;
    private boolean hasMultiargs;
    private ArrayList<FlattenedQuasiMultiterm> args;
    private boolean hasArgs;
    private StatusMap map;
    private Qoset preced;
    private boolean isAC;

    /* constructros */

    private FlattenedQuasiMultiterm(TRSTerm t, StatusMap map, Qoset preced) {
        this.tt = t;
        if (this.tt.isVariable()) {
            this.symb = null;
        } else {
            this.symb = ((TRSFunctionApplication)this.tt).getRootSymbol();
        }
    this.multiargs = null;
    this.args = null;
    this.map = map.deepcopy();
        this.preced = preced.deepcopy();

    this.hasArgs = false;
    this.hasMultiargs = false;
    if(!this.tt.isVariable()) {
            TRSFunctionApplication ftt = (TRSFunctionApplication)this.tt;
        this.isAC = map.hasFlatStatus(this.symb.getName());
        if(map.hasMultisetStatus(this.symb.getName()) || this.isAC) {
        /* the symbol has at least multiset status */
        this.hasMultiargs = true;
        this.hasArgs = false;
            this.multiargs = new HashMultiSet<FlattenedQuasiMultiterm>();
            for (TRSTerm arg : ftt.getArguments()) {
            FlattenedQuasiMultiterm s = FlattenedQuasiMultiterm.create(arg, map, preced);
            if(this.isAC && !(s.symb == null) &&
               (s.symb.equals(this.symb)
                ||  (map.hasFlatStatus(s.symb.getName()) && preced.areEquivalent(s.symb.getName(), this.symb.getName())))) {
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
        this.args = new ArrayList<FlattenedQuasiMultiterm>();
            for (TRSTerm arg : ftt.getArguments()) {
            this.args.add(FlattenedQuasiMultiterm.create(arg, map, preced));
            }
        }
    }
    }

    /** Returns a new instance of <code>FlattenedQuasiMultiterm</code>, giving multiset or AC
     * status to those symbols having it according to a status map.
     * @param t   the term that's to be transformed into a multiterm
     * @param map the status map to be used for the transformation
     */
    public static FlattenedQuasiMultiterm create(TRSTerm t, StatusMap map, Qoset preced) {
    return new FlattenedQuasiMultiterm(t, map, preced);
    }

    /** The set of terms embedded in this Multiterm through an argument
     * headed by a non-big symbol w.r.t. the precedence if this multiterm is
     * an AC multiterm.
     */
    public Set<FlattenedQuasiMultiterm> embNoBig(Qoset p) {
    if((this.symb == null) || !this.map.hasFlatStatus(this.symb.getName())) {
        return null;
    }

    Set<FlattenedQuasiMultiterm> res = new HashSet<FlattenedQuasiMultiterm>();

    /* iterate on the immediate subterms */
    Iterator<FlattenedQuasiMultiterm> e = this.multiargs.keySet().iterator();
    while(e.hasNext()) {
        FlattenedQuasiMultiterm s = e.next();
        if(!(s.symb == null)) {
        FunctionSymbol h = s.symb;
        /* no big? */
        if(!p.isGreater(h.getName(), this.symb.getName())) {
                /* iterate on the arguments of the subterm */
            Iterator<FlattenedQuasiMultiterm> ee;
            if(s.hasArgs) {
            ee = s.args.iterator();
            }
            else {
            ee = s.multiargs.keySet().iterator();
            }
            while(ee.hasNext()) {
            FlattenedQuasiMultiterm v = ee.next();
            FlattenedQuasiMultiterm elem = this.deepcopy();
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
    public MultiSet<FlattenedQuasiMultiterm> noSmallHead(Qoset p) {
    if((this.symb == null) || !this.map.hasFlatStatus(this.symb.getName())) {
        return null;
    }

    MultiSet<FlattenedQuasiMultiterm> res = new HashMultiSet<FlattenedQuasiMultiterm>();

    /* iterate on the immediate subterms */
    Iterator<FlattenedQuasiMultiterm> e = this.multiargs.keySet().iterator();
    while(e.hasNext()) {
        FlattenedQuasiMultiterm s = e.next();
        if(s.symb == null) {
        res.add(s, this.multiargs.frequency(s));
        }
        else {
        FunctionSymbol shead = s.symb;
        /* not smaller? */
        if(!p.isGreater(this.symb.getName(), shead.getName())) {
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
    public MultiSet<FlattenedQuasiMultiterm> bigHead(Qoset p) {
    if((this.symb == null) || !this.map.hasFlatStatus(this.symb.getName())) {
        return null;
    }

    MultiSet<FlattenedQuasiMultiterm> res = new HashMultiSet<FlattenedQuasiMultiterm>();

    /* iterate on the immediate subterms */
    Iterator<FlattenedQuasiMultiterm> e = this.multiargs.keySet().iterator();
    while(e.hasNext()) {
        FlattenedQuasiMultiterm s = e.next();
        if(!(s.symb == null)) {
        FunctionSymbol shead = s.symb;
        /* bigger? */
        if(p.isGreater(shead.getName(), this.symb.getName())) {
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
        FlattenedQuasiMultiterm other;
    try {
        other = (FlattenedQuasiMultiterm)o;
    }
    catch(ClassCastException e) {
        return false;
    }
        if (this.symb == null || other.symb == null) {
            return this.tt.equals(other.tt);
        }
        boolean res = this.symb.equals(other.symb);
    if(!res) {
        res = this.preced.areEquivalent(this.symb.getName(),
                       other.symb.getName())
          &&( ((FunctionSymbol)this.symb).getArity() ==
              ((FunctionSymbol)other.symb).getArity() );
    }
    if(res && (((FunctionSymbol)this.symb).getArity()==0) ) {
        return res;
    }
    if(res==true) {
        if(this.hasMultiargs && other.hasMultiargs) {
            res = this.multiargs.equals(other.multiargs);
        }
        else if(this.hasArgs && other.hasArgs) {
        Iterator i1;
        Iterator i2;
        ArrayList<FlattenedQuasiMultiterm> tmp1;
        ArrayList<FlattenedQuasiMultiterm> tmp2;
        if(this.symb.equals(other.symb)
               || ((FunctionSymbol)this.symb).getArity()==1) {
            /* compare subterms at the same positions */
                i1 = this.args.iterator();
                i2 = other.args.iterator();
        }
        else {
            /* they are only equivalent */
            if((!this.map.hasPermutation(this.symb.getName()) || !other.map.hasPermutation(other.symb.getName()))) {
                    /* we don't know how to compare the subterms */
                return false;
            }
            else {
            /* compare according to the permutations */
                Permutation p1 = this.map.getPermutation(this.symb.getName());
                Permutation p2 = other.map.getPermutation(other.symb.getName());
                tmp1 = new ArrayList<FlattenedQuasiMultiterm>();
                tmp2 = new ArrayList<FlattenedQuasiMultiterm>();
                for(int i=0; i<p1.size(); i++) {
                tmp1.add(this.args.get(p1.get(i)));
            }
                for(int i=0; i<p2.size(); i++) {
                tmp2.add(other.args.get(p2.get(i)));
                }
                i1 = tmp1.iterator();
                i2 = tmp2.iterator();
            }
        }

            FlattenedQuasiMultiterm s;
            FlattenedQuasiMultiterm t;
            while(i1.hasNext() && res==true) {
            s = (FlattenedQuasiMultiterm)i1.next();
            t = (FlattenedQuasiMultiterm)i2.next();
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
    public TRSTerm toTerm() {
    if(this.symb == null) {
        return this.tt;
    }
    String symbName = this.symb.getName();
    if(this.hasArgs) {
        ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
        Iterator i = this.args.iterator();
        while(i.hasNext()) {
        newArgs.add(((FlattenedQuasiMultiterm)i.next()).toTerm());
        }
        return TRSTerm.createFunctionApplication((FunctionSymbol)this.symb, ImmutableCreator.create(newArgs));
    }
    if(this.map.hasMultisetStatus(symbName)) {
        ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
        Iterator<FlattenedQuasiMultiterm> e = this.multiargs.keySet().iterator();
        while(e.hasNext()) {
        FlattenedQuasiMultiterm s = e.next();
        TRSTerm ss = s.toTerm();
        int n = this.multiargs.frequency(s);
        for(int i=0; i<n; i++) {
            newArgs.add(ss);
        }
        }
        return TRSTerm.createFunctionApplication((FunctionSymbol)this.symb, ImmutableCreator.create(newArgs));
    }
    if(this.map.hasFlatStatus(symbName)) {
        ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
        Iterator<FlattenedQuasiMultiterm> e = this.multiargs.keySet().iterator();
        while(e.hasNext()) {
        FlattenedQuasiMultiterm s = e.next();
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
    return TRSTerm.createFunctionApplication((FunctionSymbol)this.symb, ImmutableCreator.create(resArgs));
    }

    /** Returns a deep copy of this multiterm.
     */
    public FlattenedQuasiMultiterm deepcopy() {
    return new FlattenedQuasiMultiterm(this.toTerm(), this.map, this.preced);
    }

    /** Returns the multiarguments of this multiterms if the head symbol
     * has multiset status or AC status.
     */
    public MultiSet<FlattenedQuasiMultiterm> getMultiArguments() {
    return this.multiargs;
    }

    public ArrayList<TRSTerm> getMultiArgumentsAsTermVector() {
        ArrayList<TRSTerm> res = new ArrayList<TRSTerm>();
        for (FlattenedQuasiMultiterm tt : this.multiargs.toList()) {
            res.add(tt.toTerm());
        }
        return res;
    }

    /** Returns binary function symbols that are candidates for equivalence with this term's root.
     */
    public Set<FunctionSymbol> getReachableCandidates() {
    if((this.symb == null) || !this.map.hasFlatStatus(this.symb.getName())) {
        return null;
    }

    Set<FunctionSymbol> cands = new HashSet<FunctionSymbol>();
    Iterator<FlattenedQuasiMultiterm> e = this.multiargs.keySet().iterator();

    String thisname = this.symb.getName();

    while(e.hasNext()) {
        FlattenedQuasiMultiterm sub = e.next();

        if(!(sub.symb == null)) {
        FunctionSymbol fun = sub.symb;
            String othername = fun.getName();
        if(fun.getArity()==2 && !this.preced.isGreater(thisname, othername) && !this.preced.isGreater(othername, thisname)
           && !this.map.hasPermutation(othername) && !this.map.hasMultisetStatus(othername)) {
            cands.add(fun);
            Set<FunctionSymbol> subcands = sub.getReachableCandidates();
            if(subcands != null) {
                cands.addAll(subcands);
            }
        }
        }
    }

    return cands;
    }

    @Override
    public int hashCode() {
    return this.toString().hashCode();
    }

    public FunctionSymbol getSymbol() {
    return this.symb;
    }

    public boolean isVariable() {
    return this.tt.isVariable();
    }

    public static MultiSet<TRSTerm> toTerm(MultiSet<FlattenedQuasiMultiterm> other) {
        MultiSet<TRSTerm> res = new HashMultiSet<TRSTerm>();
        for (Map.Entry<FlattenedQuasiMultiterm,Integer> entry : other.entrySet()) {
            res.add(entry.getKey().toTerm(), entry.getValue());
        }
        return res;
    }

}
