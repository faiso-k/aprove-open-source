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

/** Implementation of the Recursive Path Order.
 *  <p>
 *  Decides whether <code>s</code> > <code>t</code> in this RPO
 *  using time O(|<code>s</code>|*|<code>t</code>|).
 *
 *  @author      Stephan Falke
 *  @version $Id$
 */

public class RPO extends AbstractNonQuasiPO implements MultisetExtensibleOrder<TRSTerm> {

    final static String orderName = "Recursive Path Order";

    private final HashOrder ho;

    /* constructors */

    private RPO(final Poset<FunctionSymbol> precedence) {
        this.precedence = precedence;
        this.ho = HashOrder.createHO();
    }

    /** Creates a new instance of <code>RPO</code>.
     * @param precedence   the precedence to be used
     */
    public static RPO create(final Poset<FunctionSymbol> precedence) {
        return new RPO(precedence);
    }

    /** Calculates the minimal extensions of <code>p</code> such that
     * <code>s >= t</code> is satisfied but not <code>s > t</code>.
     * @param leftTerm   a term
     * @param t   another term
     * @param p   a poset
     */
    public static ExtHashSetOfPosets<FunctionSymbol> minimalGENGRs(final TRSTerm origS, final TRSTerm origT, final Poset<FunctionSymbol> p) {
        ExtHashSetOfPosets<FunctionSymbol> res = ExtHashSetOfPosets.create(p.getSet());
        if(Multiterm.create(origS).equals(Multiterm.create(origT))) {
            /* the terms already are quasi-equal */
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

            final DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfPosets<FunctionSymbol>> dh = DoubleHash.create();
            TRSTerm newLeft;
            TRSTerm newRight;
            Iterator<? extends TRSTerm> i = s.getArguments().iterator();
            Iterator<? extends TRSTerm> j;

            final Poset<FunctionSymbol> tmp = p.deepcopy();
            while(i.hasNext()) {
                newLeft = i.next();
                j = t.getArguments().iterator();
                while(j.hasNext()) {
                    newRight = j.next();
                    dh.put(newLeft, newRight, RPO.minimalGENGRs(newLeft, newRight, tmp));
                }
            }


            for (final Permutation perm : PermutationGenerator.create(f.getArity())) {
                i = s.getArguments().iterator();
                ExtHashSetOfPosets<FunctionSymbol> tmpRes = ExtHashSetOfPosets.create(p.getSet());
                tmpRes.add(tmp);
                newRight = LPOS.permuteTerm(t, perm);
                j = ((TRSFunctionApplication)newRight).getArguments().iterator();
                while(i.hasNext()) {
                    try {
                        tmpRes = tmpRes.mergeAll(dh.get(i.next(), j.next())).minimalElements();
                    }
                    catch(final PosetException e) {
                        res = ExtHashSetOfPosets.create(p.getSet());
                        return res;
                    }
                }
                try {
                    res = res.union(tmpRes).minimalElements();
                }
                catch(final PosetException e) {
                    return ExtHashSetOfPosets.create(p.getSet());
                }
            }

            return res;
        }
    }

    private boolean isGENGR(final TRSTerm origS, final TRSTerm origT) {
        if(Multiterm.create(origS).equals(Multiterm.create(origT))) {
            /* the terms already are quasi-equal */
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
                    result = dh.get((TRSTerm)i.next(), (TRSTerm)j.next()).booleanValue();
                }
                if (result) {
                    break;
                }
            }

            return result;
        }
    }

    /* return 'true' if s>t in the recursive path order,
     * return 'false' otherwise.
     * The recursive path order is defined by
     *   s>t  iff  (1) not s=t
     *              and (2a) s=f(s_1, ... ,s_n) and s_j>=t for some 1<=j<=n
     *                   or
     *                  (2b) s=f(s_1, ... ,s_n), t=f(t_1, ... ,t_n) and
     *                       {s_1, ... , s_n} >> {t_1, ... , t_n}
     *                       where >> is the multiset extension
     *                   or
     *                  (2c) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_m), f|g
     *                       and s>t_i for all 1<=i<=m
     * Terms are considered equal if they differ only in a permutation of
     * their arguments.
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


    @Override
    public OrderRelation compare(final TRSTerm s, final TRSTerm t) {
        return this.calculate(s, t);
    }

    /* Returns <code>true</code> is <code>s</code> and <code>t</code>
     * are equal as multiterms.
     */
    @Override
    public boolean areEquivalent(final TRSTerm s, final TRSTerm t) {
        return Multiterm.create(s).equals(Multiterm.create(t));
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
            /* we don't know about s and t yet */
            if(Multiterm.create(origS).equals(Multiterm.create(origT))) {
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

                    if(symbLeft.equals(symbRight)) {
                        /* (2b) */
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
     * @return the implicit status map of this RPO -- compare arguments
     *  as multisets
     */
    @Override
    public StatusMap<FunctionSymbol> getStatusMap() {
        final Collection<FunctionSymbol> signature = this.precedence.getSet();
        final StatusMap<FunctionSymbol> res = StatusMap.create(signature);
        for (final FunctionSymbol f : signature) {
            res.assignMultisetStatus(f);
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
        final String res = "Recursive Path Order "+eu.cite(Citation.RPO)+"."+eu.linebreak()+"Precedence: "+eu.linebreak();
        if (eu instanceof PLAIN_Util) {
            return res+this.precedence.toString();
        } else if (eu instanceof HTML_Util) {
            return res+this.precedence.toHTML();
        } else if (eu instanceof LaTeX_Util) {
            return res+this.precedence.toLaTeX();
        } else {
            return res+this.precedence.toString();
        }
    }

}
