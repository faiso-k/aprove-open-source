package aprove.verification.dpframework.Orders ;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CSDPProblem.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.xml.*;

/**
 *   Implementation of the subterm order.
 *   <p>
 *   Decides whether <code>s</code> > <code>t</code> in the subterm
 *   order using time O(|<code>s</code>|*|<code>t</code>|).
 *
 *   @author Stephan Falke, Peter Schneider-Kamp
 *   @version $Id$
 */

public class SUB implements ExportableOrder<TRSTerm> {

    final static String orderName = "Subterm Order";

    private final HashOrder ho;

    private final ReplacementMap mu;

    public final static SUB theSUB = new SUB(null);

    /* constructors */

    private SUB(final ReplacementMap mu) {
        super();
        this.mu = mu;
        this.ho = HashOrder.createHO();
    }

    /** Creates a new instance of <code>SUB</code>.
     */
    public static SUB create(final ReplacementMap rm) {
        return new SUB(rm);
    }

    /* return 'true' if term t is a subterm of s,
     * return 'false' otherwise.
     * The subterm relation is defined by
     *   s>t  iff  (1) not s=t
     *              and (2) s=f(s_1, ... ,s_n) and s_j>=t for some 1<=j<=n
     */
    @Override
    public boolean inRelation(final TRSTerm s, final TRSTerm t) {
        return (this.calculate(s, t)==OrderRelation.GR);
    }

    @Override
    public boolean solves(final Constraint<TRSTerm> c) {
        final OrderRelation res = this.calculate(c.getLeft(),c.getRight());
        switch (c.getType()) {
        case GE:
            return res == OrderRelation.GR || res == OrderRelation.EQ || res == OrderRelation.GENGR;
        case GR:
            return res == OrderRelation.GR;
        case EQ:
            return res == OrderRelation.EQ;
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

    /* We build a hashtable with the results of comparing the relevant subterms
     * of s and t.
     */
    private OrderRelation calculate(final TRSTerm s, final TRSTerm t) {
        boolean result = false;
        OrderRelation res = this.ho.get(s, t);
        if (res != null) {
            /* we have already calculated that once */
            return res;
        } else {
            /* we don't know about s and t yet */
            if (s.equals(t)) {
                /* they are equal */
                this.ho.put(s, t, OrderRelation.EQ);
                return OrderRelation.EQ;
            } else if (s.isVariable()) {
                /* s is not greater or equal to t */
                this.ho.put(s, t, OrderRelation.NGE);
                return OrderRelation.NGE;
            } else {
                /* s = f(s_1, ..., s_n) */
                if (t.isVariable()) {
                    if (this.mu == null) {
                        result = s.getVariables().contains(t);
                    }
                    else {
                        result = this.mu.getReplacingVariables(s).contains(t);
                    }
                } else {
                    final TRSFunctionApplication fs = (TRSFunctionApplication)s;
                    /* t = g(t_1, ..., t_m) */
                    /* try (2) */
                    if (this.mu == null) {
                        final int arity = fs.getRootSymbol().getArity();
                        for (int i = 0; i < arity; ++i) {
                            final TRSTerm si = fs.getArgument(i);
                            res = this.calculate(si, t);
                            if (res == OrderRelation.EQ || res == OrderRelation.GR) {
                                result = true;
                                break;
                            }
                        }

                    }
                    else {
                        for (final Integer i : this.mu.getMap().get(fs.getRootSymbol())) {
                            final TRSTerm si = fs.getArgument(i);
                            res = this.calculate(si, t);
                            if (res == OrderRelation.EQ || res == OrderRelation.GR) {
                                result = true;
                                break;
                            }
                        }
                    }
                }
                /* update the hashtable */
                if (result == true) {
                    this.ho.put(s, t, OrderRelation.GR);
                    this.ho.put(t, s, OrderRelation.NGE);
                    return OrderRelation.GR;
                } else {
                    this.ho.put(s, t, OrderRelation.NGE);
                    return OrderRelation.NGE;
                }
            }
        }
    }

    @Override
    public String toString() {
        return "SUB";
    }

    public String toHTML() {
        return "SUB";
    }

    public String toLaTeX() {
        return "SUB";
    }

    public String toBibTeX(){
        return "";
    }

    @Override
    public String export(final Export_Util o) {
        return SUB.orderName;
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
