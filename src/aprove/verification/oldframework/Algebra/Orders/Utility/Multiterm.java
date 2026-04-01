package aprove.verification.oldframework.Algebra.Orders.Utility ;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Implementation of a multiterm, i.e. a term consisting of a root symbol
 * and a multiset of multiterms or a list of multiterms that represent the
 * arguments of the term.
 *
 *  @author  Stephan Falke
 *  @version $Id$
 */

public class Multiterm {
    private AlgebraTerm tt;
    private Symbol symb;
    private MultisetOfMultiterms multiargs;
    private boolean hasMultiargs;
    private Vector<Multiterm> args;
    private boolean hasArgs;
    private StatusMap map;
    private boolean hasMap;
    private Qoset equiv;
    private boolean hasEquiv;

    /* constructros */

    private Multiterm(AlgebraTerm t, StatusMap map, Qoset equiv) {
    this.tt = t.deepcopy();
    this.symb = this.tt.getSymbol();
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
    if(this.tt.getArguments() != null) {
        if(!this.hasMap || map.hasMultisetStatus(this.symb.getName())) {
        /* the symbol has multiset status */
        this.hasMultiargs = true;
        this.hasArgs = false;
            this.multiargs = MultisetOfMultiterms.create();
            Iterator i = this.tt.getArguments().iterator();
            while(i.hasNext()) {
            this.multiargs.add(Multiterm.create((AlgebraTerm)i.next(), map, equiv));
            }
        }
        else {
        /* the symbol has either permutation status or no status */
        this.hasArgs = true;
        this.hasMultiargs = false;
        this.args = new Vector<Multiterm>();
            Iterator i = this.tt.getArguments().iterator();
            while(i.hasNext()) {
            this.args.add(Multiterm.create((AlgebraTerm)i.next(), map, equiv));
            }
        }
    }
    }

    /** Returns a new instance of <code>Multiterm</code>, assuming that all
     * symbols have multiset status and no two distinct function symbols
     * are "equal".
     * @param t   the term that's to be transformed into a multiterm
     */
    public static Multiterm create(AlgebraTerm t) {
    return new Multiterm(t, null, null);
    }

    /** Returns a new instance of <code>Multiterm</code>, giving multiset
     * status to those symbols having it according to a status map.
     * @param t   the term that's to be transformed into a multiterm
     * @param map the status map to be used for the transformation
     */
    public static Multiterm create(AlgebraTerm t, StatusMap map) {
    return new Multiterm(t, map, null);
    }

    /** Returns a new instance of <code>Multiterm</code>, assuming that all
     * symbols have multiset status and that distinct function symbols
     * are "equal" according to a Qoset.
     * @param t   the term that's to be transformed into a multiterm
     * @param q   the qoset specifying equality between function symbols
     */
    public static Multiterm create(AlgebraTerm t, Qoset q) {
    return new Multiterm(t, null, q);
    }

    /** Returns a new instance of <code>Multiterm</code>, giving multiset
     * status to those symbols having it according to a status map and
     * asuming that distinct function symbols are "equal" according to a Qoset.
     * @param t   the term that's to be transformed into a multiterm
     * @param map the status map to be used for the transformation
     * @param q   the qoset specifying equality between function symbols
     */
    public static Multiterm create(AlgebraTerm t, StatusMap map, Qoset q) {
    return new Multiterm(t, map, q);
    }

    /** Returns <code>true</code> if this multiterm and the multiterm
     * <code>o</code> are equal, returns <code>false</code> otherwise.
     * If this multiterm was created with a qoset <code>q</code>, the
     * test is for quasi-equality.
     */
    @Override
    public boolean equals(Object o) {
        if (o == null) {
            return false;
        }
        Multiterm other;
    try {
        other = (Multiterm)o;
    }
    catch(ClassCastException e) {
        return false;
    }
    boolean res = this.symb.equals(other.symb);
    if(this.tt.isVariable() || other.tt.isVariable()) {
        return res;
    }
    if(!res && this.hasEquiv && other.hasEquiv) {
        res = this.equiv.areEquivalent(this.symb.getName(),
                       other.symb.getName())
          &&( ((SyntacticFunctionSymbol)this.symb).getArity() ==
              ((SyntacticFunctionSymbol)other.symb).getArity() );
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
        Vector<Multiterm> tmp1;
        Vector<Multiterm> tmp2;
        if(this.symb.equals(other.symb)
               || ((SyntacticFunctionSymbol)this.symb).getArity()==1) {
            /* compare subterms at the same positions */
                i1 = this.args.iterator();
                i2 = other.args.iterator();
        }
        else {
            /* they are only equivalent */
            if(this.hasMap && other.hasMap) {
                if((!this.map.hasPermutation(this.symb.getName()) || !other.map.hasPermutation(other.symb.getName()))) {
                        /* we don't know how to compare the subterms */
                    return false;
                }
                else {
                /* compare according to the permutations */
                    Permutation p1 = this.map.getPermutation(this.symb.getName());
                    Permutation p2 = other.map.getPermutation(other.symb.getName());
                    tmp1 = new Vector<Multiterm>();
                    tmp2 = new Vector<Multiterm>();
                    for(int i=0; i<p1.size(); i++) {
                    tmp1.add(this.args.elementAt(p1.get(i)));
                }
                    for(int i=0; i<p2.size(); i++) {
                    tmp2.add(other.args.elementAt(p2.get(i)));
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
    StringBuffer res = new StringBuffer(this.symb.getName());
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
    public AlgebraTerm toTerm() {
    return this.tt;
    }

    /** Returns a deep copy of this multiterm.
     */
    public Multiterm deepcopy() {
    return new Multiterm(this.tt, this.map, this.equiv);
    }

    @Override
    public int hashCode() {
    return this.toString().hashCode();
    }
}
