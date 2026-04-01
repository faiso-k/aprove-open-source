package aprove.verification.dpframework.Orders ;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.DoubleHash;
import aprove.verification.dpframework.Orders.Utility.Multiterm;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/** Implementation of the Recursive Path Order with Status.
 * <p>
 *  Decides whether <code>s</code> > <code>t</code> in this RPOS
 *  using time O(|<code>s</code>|*|<code>t</code>|).
 *
 *  @author      Stephan Falke
 *  @version $Id$
 */

public class RPOS extends AbstractNonQuasiPO implements MultisetExtensibleOrder<TRSTerm> {

    final static String orderName = "Recursive Path Order with Status";

    private final HashOrder ho;


    /* constructors */

    private RPOS(final Poset<FunctionSymbol> precedence, final StatusMap<FunctionSymbol> statusMap) {
    this.precedence = precedence;
    this.statusMap = statusMap;
    this.ho = HashOrder.createHO();
    }

    /** Creates a new instance of <code>RPOS</code>.
     * @param precedence   the precedence to be used
     * @param statusMap   the status map to be used
     */
    public static RPOS create(final Poset<FunctionSymbol> precedence, final StatusMap<FunctionSymbol> statusMap) {
    return new RPOS(precedence, statusMap);
    }

    /** Creates a new instance of <code>RPOS</code>.
     * @param status      the status to be used
     */
    public static RPOS create(final Status<FunctionSymbol> status) {
    return new RPOS(status.getPrecedence(), status.getStatusMap());
    }

    /* return 'true' if s>t in the recursive path order,
     * return 'false' otherwise.
     * The recursive path order is defined by
     *   s>t  iff  (1) not s=t
     *              and (2a) s=f(s_1, ... ,s_n) and s_j>=t for some 1<=j<=n
     *                   or
     *                  (2b) s=f(s_1, ... ,s_n), t=f(t_1, ... ,t_n) and
     *                       there exists an 1<=i<=n such that
     *                       s_p(1) = t_p(1), ... ,s_p(i-1)=t_p(i-1),
     *                       s_p(i)>t_p(i) and s>t_p(j) for all i<j<=n, if
     *                       f has permutation p as status
     *                   or
     *                  (2c) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_m), f|g
     *                       and s>t_i for all 1<=i<=m
     *                   or
     *                  (2d) s=f(s_1, ... ,s_n), t=f(t_1, ... ,t_n) and
     *                       {s_1, ... , s_n} >> {t_1, ... , t_n}
     *                       where >> is the multiset extension, if
     *                       f has multiset status
     * Terms are considered equal their multiterms according to the status map
     * are equal.
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


    @Override
    public OrderRelation compare(final TRSTerm s, final TRSTerm t) {
    return this.calculate(s, t);
    }

    /* Returns <code>true</code> is <code>s</code> and <code>t</code>
     * are equal as multiterms.
     */
    @Override
    public boolean areEquivalent(final TRSTerm s, final TRSTerm t) {
    return Multiterm.create(s, this.statusMap).equals(Multiterm.create(t, this.statusMap));
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
        if(Multiterm.create(origS, this.statusMap).equals(Multiterm.create(origT, this.statusMap))) {
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
            final TRSTerm permS = LPOS.permuteTerm(s, p);
            final TRSTerm permT = LPOS.permuteTerm(t, p);

            i = ((TRSFunctionApplication)permS).getArguments().iterator();
            j = ((TRSFunctionApplication)permT).getArguments().iterator();

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
            else if(symbLeft.equals(symbRight)
                    && this.statusMap.hasMultisetStatus(symbLeft)) {
            /* (2d) */
            final MultiSet<TRSTerm> S = new HashMultiSet<TRSTerm>(s.getArguments());
            final MultiSet<TRSTerm> T = new HashMultiSet<TRSTerm>(t.getArguments());
            final MultisetExtension mul = MultisetExtension.create(this);
            result = mul.relate(S, T)==OrderRelation.GR;
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


    /** Calculates the minimal extensions of <code>status</code> such
     * that <code>s</code> and <code>t</code> are equal as multiterms.
     */
    public static ExtHashSetOfStatuses<FunctionSymbol> minimalEqualizers(final TRSTerm s, final TRSTerm t, final Status<FunctionSymbol> stat) {
    return RPOS.minimalExt(s, t, stat, true);
    }

    /** Calculates the minimal extensions of <code>status</code> such
     * that <code>s >= t</code> is satisfied but not <code>s > t</code>
     */
    public static ExtHashSetOfStatuses<FunctionSymbol> minimalGENGRs(final TRSTerm s, final TRSTerm t, final Status<FunctionSymbol> stat) {
    return RPOS.minimalExt(s, t, stat, false);
    }

    private static ExtHashSetOfStatuses<FunctionSymbol> minimalExt(final TRSTerm origS, final TRSTerm origT, final Status<FunctionSymbol> q, final boolean eq) {
    ExtHashSetOfStatuses<FunctionSymbol> res = ExtHashSetOfStatuses.create(q.getSet());
    if(Multiterm.create(origS, q.getStatusMap()).equals(Multiterm.create(origT, q.getStatusMap()))) {
        res.add(q);
        return res;
    }
    else if(origS.isVariable()) {
        if(origT.isVariable() || eq) {
            /* no way! */
            return res;
        }
            else {
                final TRSFunctionApplication t = (TRSFunctionApplication)origT;
                final FunctionSymbol tSymb = t.getRootSymbol();
        if(tSymb.getArity()==0) {
            /* minimal constants are GE to variables */
            final Status<FunctionSymbol> statusClone = q.deepcopy();
            boolean result = false;
            try {
            statusClone.setMinimal(tSymb);
            result = true;
            }
            catch(final StatusException e) {
            /* that didn't work... */
            }
            if(result) {
            res.add(statusClone);
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


        if(q.hasPermutation(f)) {
        final Iterator i1 = s.getArguments().iterator();
        final Iterator i2 = t.getArguments().iterator();
        res.add(q);
        try {
            while(i1.hasNext() && !res.isEmpty()) {
            final Status<FunctionSymbol> tmp = res.intersectAll();
            res = res.mergeAll(RPOS.minimalExt((TRSTerm)i1.next(), (TRSTerm)i2.next(), tmp, eq)).minimalElements();
            }
        }
        catch(final StatusException e) {
            res = ExtHashSetOfStatuses.create(q.getSet());
        }

        return res;
        }
        else if(!q.hasEntry(f)) {
        /* lex */
        final Iterator i1 = s.getArguments().iterator();
        final Iterator i2 = t.getArguments().iterator();
        res.add(q);
        try {
            while(i1.hasNext() && !res.isEmpty()) {
            final Status<FunctionSymbol> tmp = res.intersectAll();
            res = res.mergeAll(RPOS.minimalExt((TRSTerm)i1.next(), (TRSTerm)i2.next(), tmp, eq)).minimalElements();
            }
        }
        catch(final StatusException e) {
            res = ExtHashSetOfStatuses.create(q.getSet());
        }

        /* multiset */
        final Status<FunctionSymbol> tmp = q.deepcopy();
        tmp.assignMultisetStatus(f);
        try {
            res = res.union(RPOS.minimalExt(s, t, tmp, eq)).minimalElements();
        }
        catch(final StatusException e) {
            res = ExtHashSetOfStatuses.create(q.getSet());
        }

        return res;
        }
        else {
        /* multiset */
        Iterator i1;
        Iterator i2;

        final DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfStatuses<FunctionSymbol>> dh = DoubleHash.create();
        i1 = s.getArguments().iterator();
        while(i1.hasNext()) {
            final TRSTerm s_i = (TRSTerm)i1.next();
            i2 = t.getArguments().iterator();
            while(i2.hasNext()) {
            final TRSTerm t_j = (TRSTerm)i2.next();
            dh.put(s_i, t_j, RPOS.minimalExt(s_i, t_j, q, eq));
            }
        }

        for (final Permutation p : PermutationGenerator.create(f.getArity())) {
            ExtHashSetOfStatuses<FunctionSymbol> tmpres = ExtHashSetOfStatuses.create(q.getSet());
            tmpres.add(q);
            try {
            for(int i=0; i<p.size(); i++) {
                tmpres = tmpres.mergeAll(dh.get(s.getArgument(i), t.getArgument(p.get(i)))).minimalElements();
            }
            res = res.union(tmpres).minimalElements();
            }
            catch(final StatusException e) {
            res = ExtHashSetOfStatuses.create(q.getSet());
            }
        }

        return res;
        }
    }
    }

    private boolean isGENGR(final TRSTerm origS, final TRSTerm origT) {
    if(Multiterm.create(origS, this.statusMap).equals(Multiterm.create(origT, this.statusMap))) {
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


        if(this.statusMap.hasPermutation(f) || !this.statusMap.hasEntry(f)) {
        final Iterator i1 = s.getArguments().iterator();
        final Iterator i2 = t.getArguments().iterator();
        boolean result = true;
        while(i1.hasNext() && result) {
            result = this.isGENGR((TRSTerm)i1.next(), (TRSTerm)i2.next());
        }
        return result;
        }
        else {
            final DoubleHash<TRSTerm,TRSTerm,Boolean> dh = DoubleHash.create();
            TRSTerm newLeft;
            TRSTerm newRight;
            Iterator i = s.getArguments().iterator();
                Iterator j;

            while(i.hasNext()) {
            newLeft = (TRSTerm)i.next();
                j = t.getArguments().iterator();
            while(j.hasNext()) {
                newRight = (TRSTerm)j.next();
                dh.put(newLeft, newRight, Boolean.valueOf(this.isGENGR(newLeft, newRight)));
            }
            }


            boolean result = false;
            for (final Permutation perm : PermutationGenerator.create(f.getArity())) {
            i = s.getArguments().iterator();
            newRight = LPOS.permuteTerm(t, perm);
            j = ((TRSFunctionApplication)newRight).getArguments().iterator();
            result = true;
            while(i.hasNext() && result) {
                result = (dh.get((TRSTerm)i.next(), (TRSTerm)j.next())).booleanValue();
            }
                    if (result) {
                        break;
                    }
            }

            return result;
        }
    }
    }

    @Override
    public String toString() {
    return Status.create(this.precedence, this.statusMap).toString();
    }


    @Override
    public String export(final Export_Util eu) {
        return "Recursive path order with status "+eu.cite(Citation.RPO)+"."
        +eu.linebreak()+Status.create(this.precedence, this.statusMap).export(eu);
    }

}
