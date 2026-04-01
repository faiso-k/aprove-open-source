package aprove.verification.dpframework.Orders ;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.PATRSProblem.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * Implementation of the subterm order modulo a collapse-free i.u.v. E.
 *
 * @author Stephan Falke
 * @version $Id$
 */

public class SubtermModE implements ExportableOrder<TRSTerm> {

    final static String orderName = "Subterm Modulo";

    private final ImmutableSet<Equation> E;
    private final HashOrder ho;
    private final Map<TRSTerm, Set<TRSTerm>> eqClasses;

    /* constructor */
    private SubtermModE(final ImmutableSet<Equation> E) {
        this.E = E;
        this.ho = HashOrder.createHO();
        this.eqClasses = new HashMap<TRSTerm, Set<TRSTerm>>();
    }

    /** Creates a new instance.
     */
    public static SubtermModE create(final ImmutableSet<Equation> E) {
        return new SubtermModE(E);
    }

    @Override
    public boolean inRelation(final TRSTerm s, final TRSTerm t) {
        return (this.calculate(s, t) == OrderRelation.GR);
    }

    @Override
    public boolean solves(final Constraint<TRSTerm> c) {
        final OrderRelation res = this.calculate(c.getLeft(),c.getRight());
        switch (c.getType()) {
        case GE:
            return res == OrderRelation.GR || res == OrderRelation.EQ;
        case GR:
            return res == OrderRelation.GR;
        case EQ:
            return res == OrderRelation.EQ;
        default:
            return false;
        }
    }

    private Set<TRSTerm> getEqClass(final TRSTerm t) {
        Set<TRSTerm> res = this.eqClasses.get(t);
        if (res == null) {
            res = new LinkedHashSet<TRSTerm>(EquivalenceClassGenerator.getEquivalenceClass(t, this.E));
            this.eqClasses.put(t, res);
        }
        return res;
    }

    @Override
    public boolean areEquivalent(final TRSTerm s, final TRSTerm t) {
        return this.getEqClass(s).contains(t);
    }

    private OrderRelation calculate(final TRSTerm s, final TRSTerm t) {
        final OrderRelation res = this.ho.get(s, t);
        if (res != null) {
            return res;
        } else {
            /* we don't know about s and t yet */
            if (this.areEquivalent(s, t)) {
                /* they are "equal" */
                this.ho.put(s, t, OrderRelation.EQ);
                this.ho.put(t, s, OrderRelation.EQ);
                return OrderRelation.EQ;
            } else if (s.isVariable()) {
                /* s is not greater or equal to t */
                this.ho.put(s, t, OrderRelation.NGE);
                return OrderRelation.NGE;
            } else {
                boolean haveGR = false;
                final Set<TRSTerm> sClass = this.getEqClass(s);
                final Set<TRSTerm> tClass = this.getEqClass(t);

                for (final TRSTerm ss : sClass) {
                    if (haveGR) {
                        break;
                    }
                    for (final TRSTerm tt : tClass) {
                        if (this.inRelationSub((TRSFunctionApplication) ss, tt)) {
                            haveGR = true;
                            break;
                        }
                    }
                }

                /* update the hashtable */
                if (haveGR) {
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

    private boolean inRelationSub(final TRSFunctionApplication s, final TRSTerm t) {
        boolean result = false;
        if (t.isVariable()) {
            result = s.getVariables().contains(t);
        } else {
            final int arr = s.getRootSymbol().getArity();
            for (int i = 0; i < arr; i++) {
                final TRSTerm si = s.getArgument(i);
                final OrderRelation res = this.calculate(si, t);
                if (res == OrderRelation.EQ || res == OrderRelation.GR) {
                    result = true;
                    break;
                }
            }
        }

        /* update the hashtable */
        if (result) {
            this.ho.put(s, t, OrderRelation.GR);
            this.ho.put(t, s, OrderRelation.NGE);
        } else {
            this.ho.put(s, t, OrderRelation.NGE);
        }

        return result;
    }

    @Override
    public String toString() {
        return "Subterm Modulo";
    }

    public String toHTML() {
        return "Subterm Modulo";
    }

    public String toLaTeX() {
        return "Subterm Modulo";
    }

    public String toBibTeX(){
        return "";
    }

    @Override
    public String export(final Export_Util o) {
        return SubtermModE.orderName;
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
