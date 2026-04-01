package aprove.verification.dpframework.Orders.Utility ;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/** Implementation of a multiterm, i.e. a term consisting of a root symbol
 * and a multiset of multiterms or a list of multiterms that represent the
 * arguments of the term.
 *
 *  @author  Stephan Falke
 *  @version $Id$
 */

public class Multiterm {
    private TRSTerm tt;
    private FunctionSymbol symb;
    private MultiSet<Multiterm> multiargs;
    private boolean hasMultiargs;
    private List<Multiterm> args;
    private boolean hasArgs;
    private StatusMap<FunctionSymbol> map;
    private boolean hasMap;
    private Qoset<FunctionSymbol> equiv;
    private boolean hasEquiv;

    /* constructros */

    private Multiterm(TRSTerm t, StatusMap<FunctionSymbol> map, Qoset<FunctionSymbol> equiv) {
    this.tt = t;
        if (this.tt.isVariable()) {
            this.symb = null;
        } else {
            this.symb = ((TRSFunctionApplication)this.tt).getRootSymbol();
        }
    this.multiargs = null;
    this.args = null;
    if(map!=null) {
        this.map = map.deepcopy();
        this.hasMap = true;
    }
    else {
        this.map = null;
        this.hasMap = false;
    }
    if(equiv!=null) {
        this.equiv = equiv.deepcopy();
        this.hasEquiv = true;
    }
    else {
        this.equiv = null;
        this.hasEquiv = false;
    }

    this.hasArgs = false;
    this.hasMultiargs = false;
    if(!this.tt.isVariable()) {
            TRSFunctionApplication ftt = (TRSFunctionApplication)this.tt;
        if(!this.hasMap || map.hasMultisetStatus(this.symb)) {
        /* the symbol has multiset status */
        this.hasMultiargs = true;
        this.hasArgs = false;
            this.multiargs = new HashMultiSet<Multiterm>();
            for (TRSTerm arg : ftt.getArguments()) {
            this.multiargs.add(Multiterm.create(arg, map, equiv));
            }
        }
        else {
        /* the symbol has either permutation status or no status */
        this.hasArgs = true;
        this.hasMultiargs = false;
        this.args = new ArrayList<Multiterm>(ftt.getArguments().size());
            for (TRSTerm arg : ftt.getArguments()) {
            this.args.add(Multiterm.create(arg, map, equiv));
            }
        }
    }
    }

    /** Returns a new instance of <code>Multiterm</code>, assuming that all
     * symbols have multiset status and no two distinct function symbols
     * are "equal".
     * @param t   the term that's to be transformed into a multiterm
     */
    public static Multiterm create(TRSTerm t) {
    return new Multiterm(t, null, null);
    }

    /** Returns a new instance of <code>Multiterm</code>, giving multiset
     * status to those symbols having it according to a status map.
     * @param t   the term that's to be transformed into a multiterm
     * @param map the status map to be used for the transformation
     */
    public static Multiterm create(TRSTerm t, StatusMap map) {
    return new Multiterm(t, map, null);
    }

    /** Returns a new instance of <code>Multiterm</code>, assuming that all
     * symbols have multiset status and that distinct function symbols
     * are "equal" according to a Qoset.
     * @param t   the term that's to be transformed into a multiterm
     * @param q   the qoset specifying equality between function symbols
     */
    public static Multiterm create(TRSTerm t, Qoset q) {
    return new Multiterm(t, null, q);
    }

    /** Returns a new instance of <code>Multiterm</code>, giving multiset
     * status to those symbols having it according to a status map and
     * asuming that distinct function symbols are "equal" according to a Qoset.
     * @param t   the term that's to be transformed into a multiterm
     * @param map the status map to be used for the transformation
     * @param q   the qoset specifying equality between function symbols
     */
    public static Multiterm create(TRSTerm t, StatusMap map, Qoset q) {
    return new Multiterm(t, map, q);
    }

    /** Returns <code>true</code> if this multiterm and the multiterm
     * <code>o</code> are equal, returns <code>false</code> otherwise.
     * If this multiterm was created with a qoset <code>q</code>, the
     * test is for quasi-equality.
     */
    @Override
    public boolean equals(Object o) {
        Multiterm other;
    try {
        other = (Multiterm)o;
    }
    catch(ClassCastException e) {
        return false;
    }
        if (this.symb == null || other.symb == null) {
            return this.tt.equals(other.tt);
        }
        boolean res = this.symb.equals(other.symb);
    if(!res && this.hasEquiv && other.hasEquiv) {
        res = this.equiv.areEquivalent(this.symb,
                       other.symb)
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
        List<Multiterm> tmp1;
        List<Multiterm> tmp2;
        if(this.symb.equals(other.symb)
               || ((FunctionSymbol)this.symb).getArity()==1) {
            /* compare subterms at the same positions */
                i1 = this.args.iterator();
                i2 = other.args.iterator();
        }
        else {
            /* they are only equivalent */
            if(this.hasMap && other.hasMap) {
                if((!this.map.hasPermutation(this.symb) || !other.map.hasPermutation(other.symb))) {
                        /* we don't know how to compare the subterms */
                    return false;
                }
                else {
                /* compare according to the permutations */
                    Permutation p1 = this.map.getPermutation(this.symb);
                    Permutation p2 = other.map.getPermutation(other.symb);
                    int n1 = p1.size();
                            int n2 = p2.size();
                            tmp1 = new ArrayList<Multiterm>(n1);
                    tmp2 = new ArrayList<Multiterm>(n2);
                    for(int i=0; i<n1; i++) {
                    tmp1.add(this.args.get(p1.get(i)));
                }
                    for(int i=0; i<n2; i++) {
                    tmp2.add(other.args.get(p2.get(i)));
                    }
                    i1 = tmp1.iterator();
                    i2 = tmp2.iterator();
                }
                }
            else {
            /* compare subterms at the same position */
            i1 = this.args.iterator();
            i2 = other.args.iterator();
            }
        }

            Multiterm s;
            Multiterm t;
            while(i1.hasNext() && res==true) {
            s = (Multiterm)i1.next();
            t = (Multiterm)i2.next();
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
            res.append(this.symb.getName());
        }
    if(this.multiargs != null) {
        res.append(this.multiargs.toString());
    }
    if(this.args != null) {
        res.append(this.args.toString());
    }
    return res.toString();
    }

    /** Returns the term that was used to create this multiterm.
     */
    public TRSTerm toTerm() {
    return this.tt;
    }

    /** Returns a deep copy of this multiterm.
     */
    public Multiterm deepcopy() {
    return new Multiterm(this.tt, this.map, this.equiv);
    }

    @Override
    public int hashCode() {
    return (this.hasMultiargs ? this.multiargs.hashCode() : 0) + (this.hasArgs ? this.args.hashCode() : 0);
    }
}
