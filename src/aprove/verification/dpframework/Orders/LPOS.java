package aprove.verification.dpframework.Orders ;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/** Implementation of the Lexicographic Path Order with Status.
 * <p>
 *  Decides whether <code>s</code> > <code>t</code> in this LPOS
 *  using time O(|<code>s</code>|*|<code>t</code>|).
 *
 *  @author      Stephan Falke
 *  @version $Id$
 */

public class LPOS extends AbstractNonQuasiPO {

    final static String orderName = "Lexicographic Path Order with Status";

    private final HashOrder ho;


    /* constructors */

    private LPOS(final Poset<FunctionSymbol> precedence, final StatusMap<FunctionSymbol> statusMap) {
        this.precedence = precedence;
        this.statusMap = statusMap;
        this.ho = HashOrder.createHO();
    }

    /** Creates a new instance of <code>LPOS</code>.
     * @param signature   the names of the symbols
     * @param precedence   the precedence to be used
     * @param statusMap   the status map to be used
     */
    public static LPOS create(final Poset<FunctionSymbol> precedence, final StatusMap<FunctionSymbol> statusMap) {
        return new LPOS(precedence, statusMap);
    }

    /** Creates a new instance of <code>LPOS</code>.
     * @param signature   the names of the symbols
     * @param status      the status to be used
     */
    public static LPOS create(final Status<FunctionSymbol> status) {
        return new LPOS(status.getPrecedence(), status.getStatusMap());
    }

    /** Calculates the minimal extensions of <code>stat</code> such that
     * <code>s >= t</code> is satisfied but not <code>s > t</code>.
     * @param s   a term
     * @param t   another term
     * @param stat   a status
     */
    public static ExtHashSetOfStatuses<FunctionSymbol> minimalGENGRs(final TRSTerm s, final TRSTerm t, final Status<FunctionSymbol> stat) {
        final ExtHashSetOfPosets<FunctionSymbol> res1 = LPO.minimalGENGRs(s, t, stat.getPrecedence());
        final ExtHashSetOfStatuses<FunctionSymbol> res = ExtHashSetOfStatuses.create(stat.getSet());

        final Iterator<Poset<FunctionSymbol>> i = res1.iterator();
        while(i.hasNext()) {
            final Poset<FunctionSymbol> p = i.next();
            res.add(Status.create(p, stat.getStatusMap()));
        }

        return res;
    }

    /** Applies a permutation to a term.
     * @param t   the term to be permuted
     * @param p   the permutation to be used
     */
    public static TRSFunctionApplication permuteTerm(final TRSFunctionApplication t, final Permutation p) {
        final List<? extends TRSTerm> args = t.getArguments();
        final ArrayList<TRSTerm> permArgs = new ArrayList<TRSTerm>();
        for(int i=0; i<p.size(); i++) {
            permArgs.add( args.get( p.get( i )));
        }
        final FunctionSymbol sym = t.getRootSymbol();
        return TRSTerm.createFunctionApplication(sym, ImmutableCreator.create(permArgs));
    }


    /* return 'true' if s>t in the lexicographic path order,
     * return 'false' otherwise.
     * The lexicographic path order is defined by
     *   s>t  iff  (1) not s=t
     *              and (2a) s=f(s_1, ... ,s_n) and s_j>=t for some 1<=j<=n
     *                   or
     *                  (2b) s=f(s_1, ... ,s_n), t=f(t_1, ... ,t_n) and
     *                       there exists an 1<=i<=n such that
     *                       s_p(1) = t_p(1), ... ,s_p(i-1)=t_p(i-1),
     *                       s_p(i)>t_p(i) and s>t_p(j) for all i<j<=n
     *                   or
     *                  (2c) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_m), f|g
     *                       and s>t_i for all 1<=i<=m
     */
    @Override
    public boolean inRelation(final TRSTerm s, final TRSTerm t) {
        this.calculate(s, t);
        return (this.ho.get(s, t)==OrderRelation.GR);
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

    private boolean isGENGR(final TRSTerm origS, final TRSTerm origT) {
        if(origS.equals(origT)) {
            /* the terms are equal */
            return true;
        }
        else if(origS.isVariable()) {
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
        else if(origT.isVariable()) {
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

    /* We build a hashtble with the results of comparing the relevant subterms
     * of s and t.
     */
    private OrderRelation calculate(final TRSTerm origS, final TRSTerm origT) {
        boolean result=false;
        OrderRelation res;

        res = this.ho.get(origS, origT);
        if(res != null) {
            /* we already know it */
            return res;
        }
        else {
            if(EMB.theEMB.inRelation(origS, origT)) {
                this.ho.put(origS, origT, OrderRelation.GR);
                this.ho.put(origT, origS, OrderRelation.NGE);
                return OrderRelation.GR;
            }

            /* we don't know about s and t yet */
            if(origS.equals(origT)) {
                /* they are equal */
                this.ho.put(origS, origT, OrderRelation.EQ);
                return OrderRelation.EQ;
            }
            else if(origS.isVariable()) {
                result=this.isGENGR(origS, origT);
                if(result) {
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

                    if(symbLeft.equals(symbRight)
                            && symbLeft.getArity()==1) {
                        res = this.calculate(s.getArgument(0), t.getArgument(0));
                        result = (res==OrderRelation.GR);
                    }
                    else if(symbLeft.equals(symbRight)
                            && this.statusMap.hasPermutation(symbLeft)) {

                        /* apply permutation */
                        final Permutation p = this.statusMap.getPermutation(symbLeft);
                        final TRSFunctionApplication permS = LPOS.permuteTerm(s, p);
                        final TRSFunctionApplication permT = LPOS.permuteTerm(t, p);

                        i = permS.getArguments().iterator();
                        j = permT.getArguments().iterator();

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
                        /* f and g are incomparable or g | f
                         * or no statuses.
                         * We can only hope for (2a) */
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

    @Override
    public String export(final Export_Util eu) {
        return "Lexicographic path order with status "+eu.cite(Citation.LPO)+"."
        +eu.linebreak()+Status.create(this.precedence, this.statusMap).export(eu);
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

}
