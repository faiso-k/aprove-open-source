package aprove.verification.dpframework.Orders ;

import java.util.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;

/**
 *   Implementation of the basic simplification order, namely the
 *   (homeomorphic) embedding order.
 *   <p>
 *   Decides whether <code>s</code> > <code>t</code> in the embedding
 *   order using time O(|<code>s</code>|*|<code>t</code>|).
 *
 *   @author Stephan Falke
 *   @version $Id$
 */

public class EMB implements CPFExportableAfsOrder {

    final static Logger log = Logger.getLogger("aprove.verification.dpframework.Orders.EMB");

    final static String orderName = "Homeomorphic Embedding Order";

    private final HashOrder ho;

    public final static EMB theEMB = new EMB();

    /* constructors */

    private EMB() {
        super();
        this.ho = HashOrder.createHO();
    }

    /** Creates a new instance of <code>EMB</code>.
     */
    public static EMB create() {
    return EMB.theEMB;
    }

    /* return 'true' if term t is homeomorphicly embedded in term t,
     * return 'false' otherwise.
     * The homeomorphic embedding is defined by
     *   s>t  iff  (1) not s=t
     *              and (2a) s=f(s_1, ... ,s_n) and s_j>=t for some 1<=j<=n
     *                   or
     *                  (2b) s=f(s_1, ... ,s_n), t=f(t_1, ... ,t_n) and
     *                       s_1>=t_1, ... , s_n>=t_n
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
        return res == needed;
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
        EMB.log.log(Level.FINER,"EMB: s = {0}, t = {1}\n",new Object[] {origS, origT});
        boolean result=false;
        OrderRelation res;

        res = this.ho.get(origS, origT);
        if (res!=null) {
            EMB.log.finest("EMB: we have already calculated that once\n");
            /* we have already calculated that once */
            EMB.log.log(Level.FINER,"EMB: result is {0}\n",res);
            return res;
        }
        else {
            EMB.log.finest("EMB: we don't know about s and t yet\n");
            /* we don't know about s and t yet */
            if (origS.equals(origT)) {
                EMB.log.finest("EMB: they are equal\n");
                /* they are equal */
                this.ho.put(origS, origT, OrderRelation.EQ);
                EMB.log.log(Level.FINER,"EMB: result is {0}\n",OrderRelation.EQ);
                return OrderRelation.EQ;
            }
            else if(origS instanceof TRSVariable) {
                EMB.log.finest("EMB: s is not greater or equal to t\n");
        /* s is not greater or equal to t */
                this.ho.put(origS, origT, OrderRelation.NGE);
                EMB.log.log(Level.FINER,"EMB: result is {0}\n",OrderRelation.NGE);
                return OrderRelation.NGE;
            }
            else {
                final TRSFunctionApplication s = (TRSFunctionApplication)origS;
                EMB.log.finest("EMB: s = f(s_1, ..., s_n)\n");
                /* s = f(s_1, ..., s_n) */
                if (origT instanceof TRSVariable) {
                    result = s.getVariables().contains(origT);
                }
                else {
                    final TRSFunctionApplication t = (TRSFunctionApplication)origT;
                    EMB.log.finest("EMB: t = g(t_1, ..., t_m)\n");
                    /* t = g(t_1, ..., t_m) */
                    Iterator i;

                    if (s.getRootSymbol().equals(t.getRootSymbol())) {
                        EMB.log.finest("EMB: if s and t have the same root symbol we compare the i'th subterm of s with the i'th subterm of t\n");
                        /* if s and t have the same root symbol we compare
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
                                EMB.log.finest("EMB: s_i EQ t_i ==> s GR t_i, t GR s_i\n");
                                /* s_i EQ t_i ==> s GR t_i, t GR s_i */
                                this.ho.put(s, t_i, OrderRelation.GR);
                this.ho.put(t_i, s, OrderRelation.NGE);
                this.ho.put(t, s_i, OrderRelation.GR);
                this.ho.put(s_i, t, OrderRelation.NGE);
                }
                else {
                                EMB.log.finest("EMB: s_i GR t_i ==> s GR t_i\n");
                /* s_i GR t_i ==> s GR t_i */
                this.ho.put(s, t_i, OrderRelation.GR);
                this.ho.put(t_i, s, OrderRelation.NGE);
                }
            }
            if(result==false) {
                            EMB.log.finest("EMB: (2b) not successfull, so try a (partial) (2a)\n");
                /* (2b) not successfull, so try a (partial) (2a) */
                i = s.getArguments().iterator();
                j = t.getArguments().iterator();

                result = false;
                while(i.hasNext() && result==false) {
                s_i = (TRSTerm)i.next();
                t_i = (TRSTerm)j.next();
                res = this.ho.get(s_i, t_i);
                if(res==null || res==OrderRelation.GR) {
                                    EMB.log.finest("EMB: no use to do the test otherwise\n");
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
                        EMB.log.finest("EMB: f != g\nEMB: try (2a)\n");
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

                EMB.log.finest("EMB: update the hashtable\n");
        /* update the hashtable */
        if(result==true) {
            this.ho.put(s, origT, OrderRelation.GR);
                    this.ho.put(origT, s, OrderRelation.NGE);
                    EMB.log.log(Level.FINER,"EMB: result is {0}\n",OrderRelation.GR);
            return OrderRelation.GR;
        }
        else {
            this.ho.put(s, origT, OrderRelation.NGE);
                    EMB.log.log(Level.FINER,"EMB: result is {0}\n",OrderRelation.NGE);
            return OrderRelation.NGE;
        }
        }
    }
    }


    @Override
    public String toString() {
    return "EMB rules!";
    }

    @Override
    public String export(final Export_Util o) {
        return EMB.orderName;
    }


    @Override
    public String isCPFSupported() {
        return null;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        return this.toCPF(doc, xmlMetaData, new HashSet<FunctionSymbol>(), null);
    }


    @Override
    public Element toCPF(Document doc, XMLMetaData xmlMetaData,
            Iterable<FunctionSymbol> fs, Afs afs) {
        final Set<FunctionSymbol> sig = new HashSet<FunctionSymbol>();
        if (afs != null) {
            for (FunctionSymbol f : fs) {
                final FunctionSymbol filteredF = afs.filter(f);
                if (filteredF != null) {
                    sig.add(filteredF);
                }
            }
        }
        return LPO.create(Poset.create(sig)).toCPF(doc, xmlMetaData, fs, afs);
    }

}
