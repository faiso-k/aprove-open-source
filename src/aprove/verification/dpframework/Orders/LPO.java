package aprove.verification.dpframework.Orders;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

/** Implementation of the Lexicographic Path Order.
 *  <p>
 *  Decides whether <code>s</code> > <code>t</code> in this LPO
 *  using time O(|<code>s</code>|*|<code>t</code>|).
 *
 *  @author      Stephan Falke
 *  @version $Id$
 */

public class LPO extends AbstractNonQuasiPO {

    final static String orderName = "Lexicographic Path Order";

    private final HashOrder ho;

    /* constructors */

    private LPO(final Poset<FunctionSymbol> precedence) {
    this.precedence = precedence;
    this.ho = HashOrder.createHO();
    }

    /** Creates a new instance of <code>LPO</code>.
     * @param signature   the names of the symbols
     * @param precedence   the precedence to be used
     */
    public static LPO create(final Poset<FunctionSymbol> precedence) {
    return new LPO(precedence);
    }

    /** Creates a new empty instance of <code>LPO</code>.
     */
    public static LPO create() {
    final List<FunctionSymbol> sicksig = new ArrayList<FunctionSymbol>();
    return new LPO(Poset.create(sicksig));
    }

    /** Calculates the minimal extensions of <code>p</code> such that
     * <code>s >= t</code> is satisfied but not <code>s > t</code>.
     * @param leftTerm   a term
     * @param t   another term
     * @param p   a poset
     */
    public static ExtHashSetOfPosets<FunctionSymbol> minimalGENGRs(final TRSTerm origS, final TRSTerm origT, final Poset<FunctionSymbol> p) {
    ExtHashSetOfPosets<FunctionSymbol> res = ExtHashSetOfPosets.create(p.getSet());
    if(origS.equals(origT)) {
        /* the terms already are equal */
        res.add(p);
        return res;
    }
    else if(origS.isVariable()) {
        if(origT.isVariable()) {
            /* no way! */
            return res;
        }
            else {
                final TRSFunctionApplication t = (TRSFunctionApplication)origT;
            final FunctionSymbol tSymb = t.getRootSymbol();
        if(tSymb.getArity()==0) {
            /* minimal constants are GE to variables */
            final Poset<FunctionSymbol> precedenceClone = p.deepcopy();
            boolean result = false;
            try {
            precedenceClone.setMinimal(tSymb);
            result = true;
            }
            catch(final PosetException e) {
            /* that didn't work... */
            }
            if(result) {
            res.add(precedenceClone);
            }
        }
        return res;
        }
    }
    else if(origT.isVariable()) {
        /* no way */
        return res;
    }
        else {
            final TRSFunctionApplication s = (TRSFunctionApplication)origS;
            final TRSFunctionApplication t = (TRSFunctionApplication)origT;
        /* s = f(s_1, ..., s_n), t = g(t_1, ..., t_m) */
        final FunctionSymbol f = s.getRootSymbol();
        final FunctionSymbol g = t.getRootSymbol();

        if(!f.equals(g)) {
            /* no way! */
            return res;
        }

        final Iterator i = s.getArguments().iterator();
        final Iterator j = t.getArguments().iterator();
        res.add(p.deepcopy());

        while(i.hasNext() && !res.isEmpty()) {
        try {
            res = res.mergeAll(LPO.minimalGENGRs((TRSTerm)i.next(),
                              (TRSTerm)j.next(),
                              res.intersectAll())).minimalElements();
        }
        catch(final PosetException e) {
            return ExtHashSetOfPosets.create(p.getSet());
        }
        }
        return res;
    }
    }

    private boolean isGENGR(final TRSTerm origS, final TRSTerm origT) {
    if(origS.equals(origT)) {
        /* the terms are equal */
        return true;
    }
    else if (origS.isVariable()) {
        if(origT.isVariable()) {
            /* no way! */
            return false;
        }
            else {
                final TRSFunctionApplication t = (TRSFunctionApplication)origT;
            final FunctionSymbol tSymb = t.getRootSymbol();
        if(tSymb.getArity()==0) {
            /* minimal constants are GE to variables */
            return this.precedence.isMinimal(tSymb);
        }
        return false;
        }
    }
    else if (origT.isVariable()) {
        /* no way */
        return false;
    }
        else {
            final TRSFunctionApplication s = (TRSFunctionApplication)origS;
            final TRSFunctionApplication t = (TRSFunctionApplication)origT;
        /* s = f(s_1, ..., s_n), t = g(t_1, ..., t_m) */
        final FunctionSymbol f = s.getRootSymbol();
        final FunctionSymbol g = t.getRootSymbol();

        if(!f.equals(g)) {
            /* no way! */
            return false;
        }

        final Iterator i = s.getArguments().iterator();
        final Iterator j = t.getArguments().iterator();

        boolean result = true;
        while(i.hasNext() && result) {
        result = this.isGENGR((TRSTerm)i.next(), (TRSTerm)j.next());
        }
        return result;
    }
    }

    /* return 'true' if s>t in the lexicographic path order,
     * return 'false' otherwise.
     * The lexicographic path order is defined by
     *   s>t  iff  (1) not s=t
     *              and (2a) s=f(s_1, ... ,s_n) and s_j>=t for some 1<=j<=n
     *                   or
     *                  (2b) s=f(s_1, ... ,s_n), t=f(t_1, ... ,t_n) and
     *                       there exists an 1<=i<=n such that
     *                       s_1 = t_1, ... ,s_i-1=t_i-1, s_i>t_i and
     *                       s>t_j for all i<j<=n
     *                   or
     *                  (2c) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_m), f|g
     *                       and s>t_i for all 1<=i<=m
     */
     @Override
    public boolean inRelation(final TRSTerm s, final TRSTerm t) {
    return (this.calculate(s, t)==OrderRelation.GR);
    }

    @Override
    public boolean solves(final Constraint<TRSTerm> c) {
        final OrderRelation res = this.calculate(c.getLeft(),c.getRight());
        final OrderRelation needed = c.getType();
        if (needed == OrderRelation.GE) {
            return (res == OrderRelation.GR || res == OrderRelation.EQ || res == OrderRelation.GENGR);
        }
        if (needed == OrderRelation.GR) {
            return (res == OrderRelation.GR);
        }
        if (needed == OrderRelation.EQ) {
            return (res == OrderRelation.EQ);
        }
        return false;
    }

    /* Returns <code>true</code> is <code>s</code> and <code>t</code>
     * are syntactically equal.
     */
    @Override
    public boolean areEquivalent(final TRSTerm s, final TRSTerm t) {
    return s.equals(t);
    }

    /* We build a hashtble with the results of comparing the relevant subterms
     * of s and t.
     */
    private OrderRelation calculate(final TRSTerm origS, final TRSTerm origT) {
    boolean result=false;
    OrderRelation res;

    res = this.ho.get(origS, origT);
    if(res!=null) {
        /* we already know it */
        return res;
    }
    else {
        /* we don't know about s and t yet */
        if(origS.equals(origT)) {
        /* they are equal */
        this.ho.put(origS, origT, OrderRelation.EQ);
        return OrderRelation.EQ;
        }
        else if(origS.isVariable()) {
        result=this.isGENGR(origS, origT);
        if (result) {
            this.ho.put(origS, origT, OrderRelation.GENGR);
            return OrderRelation.GENGR;
        }
        else {
            this.ho.put(origS, origT, OrderRelation.NGE);
            return OrderRelation.NGE;
        }
        }
            else {
                final TRSFunctionApplication s = (TRSFunctionApplication)origS;
        /* s = f(s_1), ..., s_n) */
        if(origT.isVariable()) {
            result = s.getVariables().contains(origT);
        }
                else {
                    final TRSFunctionApplication t = (TRSFunctionApplication)origT;
            /* t = g(t_1, ..., t_m) */
            Iterator i;
            Iterator j;

            final FunctionSymbol symbLeft = s.getRootSymbol();
            final FunctionSymbol symbRight = t.getRootSymbol();

            TRSTerm s_i;
            TRSTerm t_i;

            if(symbLeft.equals(symbRight)) {
            i = s.getArguments().iterator();
            j = t.getArguments().iterator();

            s_i = (TRSTerm)i.next();
            t_i = (TRSTerm)j.next();
            /* skip equal subterms s_i = t_i or s_i >= t_i*/
            res = this.calculate(s_i, t_i);
            while(i.hasNext() && (res==OrderRelation.EQ || res==OrderRelation.GENGR)) {
                s_i = (TRSTerm)i.next();
                t_i = (TRSTerm)j.next();
                res = this.calculate(s_i, t_i);
            }

            if(!i.hasNext() && (res==OrderRelation.EQ || res==OrderRelation.GENGR)) {
                /* out of arguments */
                this.ho.put(s, t, OrderRelation.GENGR);
                return OrderRelation.GENGR;
            }

            /* now, s_i != t_i */
                res = this.calculate(s_i, t_i);
            if(res==OrderRelation.GR) {
                /* s_i GR t_i */
                /* continue (2b), no need to do (2a) */
                /* s_i GR t_i ==> s GR t_i */
                this.ho.put(s, t_i, OrderRelation.GR);
                this.ho.put(t_i, s, OrderRelation.NGE);

                result = true;
                while(j.hasNext() && result==true) {
                t_i = (TRSTerm)j.next();
                res = this.calculate(s, t_i);
                if(res!=OrderRelation.GR) {
                    if(res==OrderRelation.EQ) {
                    /* s EQ t_i ==> t GR s */
                    this.ho.put(t, s, OrderRelation.GR);
                    }
                    result = false;
                }
                }
            }
            else {
                /* s_i NGE t_i */
                /* check (2a) for s_i+1, ..., s_n */
                result = false;
                while(i.hasNext() && result== false) {
                s_i = (TRSTerm)i.next();
                res = this.calculate(s_i, t);
                if(res==OrderRelation.EQ || res==OrderRelation.GR || res==OrderRelation.GENGR) {
                    result = true;
                }
                }
            }
            }
            else if(this.precedence.isGreater(symbLeft, symbRight)) {
            /* f | g */
            /* (2c), no need for (2a) in this case */
                j = t.getArguments().iterator();

            result = true;
            while(j.hasNext() && result==true) {
                t_i = (TRSTerm)j.next();
                res = this.calculate(s, t_i);
                if(res!=OrderRelation.GR) {
                if(res==OrderRelation.EQ) {
                    /* s EQ t_j ==> t GR s */
                    this.ho.put(t, s, OrderRelation.GR);
                }
                result = false;
                }
            }
            }
            else {
            /* f and g are incomparable or g | f*/
            /* we can only hope for (2a) */
            i = s.getArguments().iterator();

            result = false;
            while(i.hasNext() && result==false) {
                s_i = (TRSTerm)i.next();
                res = this.calculate(s_i, t);
                if(res==OrderRelation.EQ || res==OrderRelation.GR || res==OrderRelation.GENGR) {
                result = true;
                }
            }
            }
        }

        /* update the hashtable */
        if(result==true) {
            this.ho.put(s, origT, OrderRelation.GR);
            this.ho.put(origT, s, OrderRelation.NGE);
            return OrderRelation.GR;
        }
        else {
            result=this.isGENGR(s, origT);
            if(result) {
                this.ho.put(s, origT, OrderRelation.GENGR);
                return OrderRelation.GENGR;
            }
            else {
            this.ho.put(s, origT, OrderRelation.NGE);
            return OrderRelation.NGE;
            }
        }
        }
    }
    }

    /**
     * @return the implicit status map of this LPO -- compare arguments
     *  lexicographically left-to-right
     */
    @Override
    public StatusMap<FunctionSymbol> getStatusMap() {
        final Collection<FunctionSymbol> signature = this.precedence.getSet();
        final StatusMap<FunctionSymbol> res = StatusMap.create(signature);
        for (final FunctionSymbol f : signature) {
            final int n = f.getArity();
            final Permutation leftToRight = Permutation.createLeftToRight(n);
            res.assignPermutation(f, leftToRight);
        }
        return res;
    }

    @Override
    public String toString() {
        final StringBuilder result = new StringBuilder();
        result.append("Precedence:\n");
        result.append(this.precedence.toString());
        return result.toString();
    }

    @Override
    public String export(final Export_Util eu) {
        return "Lexicographic Path Order "+eu.cite(Citation.LPO)+"."+
          eu.linebreak()+"Precedence: "+eu.linebreak()+this.precedence.export(eu);
    }

    public Object toCodish(final FreshNameGenerator vars, final FreshNameGenerator funcs) {
        return Poset.toCodish(this.precedence, vars, funcs);
    }

}
