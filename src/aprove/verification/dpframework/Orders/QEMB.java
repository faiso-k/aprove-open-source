package aprove.verification.dpframework.Orders ;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;

/**
 *   Implementation of the basic simplification order, namely the
 *   (homeomorphic) embedding order (here, with equivalence of distinct
 *   function symbols).
 *   <p>
 *   Decides whether <code>s</code> > <code>t</code> in the embedding
 *   order using time O(|<code>s</code>|*|<code>t</code>|).
 *
 *   @author Stephan Falke
 *   @version $Id$
 */

public class QEMB implements ExportableOrder<TRSTerm> {

    final static String orderName = "Homeomorphic Embedding Order with Non-Strict Precedence";

    private final HashOrder ho;
    private final Qoset<FunctionSymbol> equiv;


    /* constructors */

    private QEMB(final Qoset<FunctionSymbol> equiv) {
        super();
        this.ho = HashOrder.createHO();
        this.equiv = equiv;
    }

    /** Creates a new instance of <code>QEMB</code>.
     *  @param equiv   the qoset containing equivalences between function symbols
     */
    public static QEMB create(final Qoset<FunctionSymbol> equiv) {
        return new QEMB(equiv);
    }

    /** Returns the used precedence.
     */
    public OrderedSet<FunctionSymbol> getPrecedence() {
        return this.equiv;
    }

    /* return 'true' if term t is homeomorphicly embedded in term t,
     * return 'false' otherwise.
     * The homeomorphic embedding is defined by
     *   s>t  iff  (1) not s=t
     *              and (2a) s=f(s_1, ... ,s_n) and s_j>=t for some 1<=j<=n
     *                   or
     *                  (2b) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_n) and
     *                       s_1>=t_1, ... , s_n>=t_n where f and g are
     *                       equivalent
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
     * are syntactically equal up to equivalent symbols.
     */
    @Override
    public boolean areEquivalent(final TRSTerm s, final TRSTerm t) {
        return QLPO.quasiEqual(s, t, this.equiv);
    }

    /* We build a hashtble with the results of comparing the relevant subterms
     * of s and t.
     */
    private OrderRelation calculate(final TRSTerm origS, final TRSTerm origT) {
        boolean result=false;
        OrderRelation res;

        res = this.ho.get(origS, origT);
        if(res != null) {
            /* we have already calculated that once */
            return res;
        }
        else {
            /* we don't know about s and t yet */
            if(QLPO.quasiEqual(origS, origT, this.equiv)) {
                /* they are equal */
                this.ho.put(origS, origT, OrderRelation.EQ);
                return OrderRelation.EQ;
            }
            else if(origS.isVariable()) {
                /* s is not greater or equal to t */
                this.ho.put(origS, origT, OrderRelation.NGE);
                return OrderRelation.NGE;
            }
            else {
                final TRSFunctionApplication s = (TRSFunctionApplication)origS;
                /* s = f(s_1, ..., s_n) */
                if(origT.isVariable()) {
                    result = s.getVariables().contains(origT);
                }
                else {
                    final TRSFunctionApplication t = (TRSFunctionApplication)origT;
                    /* t = g(t_1, ..., t_m) */
                    Iterator i;

                    if(s.getRootSymbol().equals(t.getRootSymbol())
                            ||
                            (this.equiv.areEquivalent(s.getRootSymbol(), t.getRootSymbol())
                                    &&
                                    (s.getRootSymbol()).getArity()==(t.getRootSymbol()).getArity())) {
                        /* if s and t have equivalent root symbol we compare
                         * the i'th subterm of s with the i'th subterm of t
                         */

                        Iterator j;

                        i = s.getArguments().iterator();
                        j = t.getArguments().iterator();
                        TRSTerm s_i;
                        TRSTerm t_i;

                        result = true;
                        while(i.hasNext() && result==true) {
                            s_i = (TRSTerm)i.next();
                            t_i = (TRSTerm)j.next();
                            res = this.calculate(s_i, t_i);
                            if(res==OrderRelation.NGE) {
                                result = false;
                            }
                            else if(res==OrderRelation.EQ) {
                                /* s_i EQ t_i ==> s GR t_i, t GR s_i */
                                this.ho.put(s, t_i, OrderRelation.GR);
                                this.ho.put(t_i, s, OrderRelation.NGE);
                                this.ho.put(t, s_i, OrderRelation.GR);
                                this.ho.put(s_i, t, OrderRelation.NGE);
                            }
                            else {
                                /* s_i GR t_i ==> s GR t_i */
                                this.ho.put(s, t_i, OrderRelation.GR);
                                this.ho.put(t_i, s, OrderRelation.NGE);
                            }
                        }
                        if(result==false) {
                            /* (2b) not successfull, so try a (partial) (2a) */
                            i = s.getArguments().iterator();
                            j = t.getArguments().iterator();

                            result = false;
                            while(i.hasNext() && result==false) {
                                s_i = (TRSTerm)i.next();
                                t_i = (TRSTerm)j.next();
                                res = this.ho.get(s_i, t_i);
                                if(res== null || res==OrderRelation.GR) {
                                    /* no use to do the test otherwise */
                                    res = this.calculate(s_i, t);
                                    if(res==OrderRelation.EQ || res==OrderRelation.GR) {
                                        result = true;
                                    }
                                }
                            }
                        }
                    }
                    else {
                        /* f != g */
                        /* try (2a) */
                        i = s.getArguments().iterator();
                        TRSTerm s_i;

                        result = false;
                        while(i.hasNext() && result==false) {
                            s_i = (TRSTerm)i.next();
                            res = this.calculate(s_i, t);
                            if(res==OrderRelation.EQ || res==OrderRelation.GR) {
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
                    this.ho.put(s, origT, OrderRelation.NGE);
                    return OrderRelation.NGE;
                }
            }
        }
    }

    @Override
    public String export(final Export_Util eu) {
        return "Embedding order with quasi-precedence. "+eu.linebreak()+
        "Precedence: "+this.equiv.export(eu)+eu.linebreak();
    }


    @Override
    public String toString() {
        return this.equiv.toString();
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        throw new RuntimeException("no CPF export " + this.isCPFSupported());
    }

    @Override
    public String isCPFSupported() {
        return this.getClass().getCanonicalName();
    }

}
