package aprove.verification.dpframework.Orders;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.Multiterm;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/** Multiset extension of a <code>MultisetExtensibleOrder</code>.
 * <p>
 * Only tested with <code>RPO</code>, <code>RPOS</code>, <code>QRPOS</code>
 * and <code>QRPOS</code>.
 *
 * @see MultisetExtensibleOrder
 * @author Stephan Falke
 * @version $Id$
 */

public class MultisetExtension {

    private MultisetExtensibleOrder<TRSTerm> order;
    private MultiSet<TRSTerm> left;
    private MultiSet<TRSTerm> right;

    /* constructors */

    private MultisetExtension(MultisetExtensibleOrder<TRSTerm> order) {
    this.order = order;
    this.left = new HashMultiSet<TRSTerm>();
    this.right = new HashMultiSet<TRSTerm>();
    }

    /** Returns a new instance of <code>MultisetExtension</code>.
     * @param order   the order that's to be used by this multiset extension
     */
    public static MultisetExtension create(MultisetExtensibleOrder<TRSTerm> order) {
    return new MultisetExtension(order);
    }

    private static MultiSet<Multiterm> toMultiterm(MultiSet<TRSTerm> from) {
        MultiSet<Multiterm> res = new HashMultiSet<Multiterm>();
        for (Map.Entry<TRSTerm,Integer> entry : from.entrySet()) {
            res.add(Multiterm.create(entry.getKey()), entry.getValue());
        }
        return res;
    }

    private static MultiSet<Multiterm> toMultiterm(MultiSet<TRSTerm> from, Qoset<FunctionSymbol> equiv) {
        MultiSet<Multiterm> res = new HashMultiSet<Multiterm>();
        for (Map.Entry<TRSTerm,Integer> entry : from.entrySet()) {
            res.add(Multiterm.create(entry.getKey(), equiv), entry.getValue());
        }
        return res;
    }

    private static MultiSet<Multiterm> toMultiterm(MultiSet<TRSTerm> from, StatusMap map) {
        MultiSet<Multiterm> res = new HashMultiSet<Multiterm>();
        for (Map.Entry<TRSTerm,Integer> entry : from.entrySet()) {
            res.add(Multiterm.create(entry.getKey(), map), entry.getValue());
        }
        return res;
    }

    private static MultiSet<Multiterm> toMultiterm(MultiSet<TRSTerm> from, StatusMap map, Qoset<FunctionSymbol> equiv) {
        MultiSet<Multiterm> res = new HashMultiSet<Multiterm>();
        for (Map.Entry<TRSTerm,Integer> entry : from.entrySet()) {
            res.add(Multiterm.create(entry.getKey(), map, equiv), entry.getValue());
        }
        return res;
    }

    private static MultiSet<TRSTerm> fromMultiterm(MultiSet<Multiterm> from) {
        MultiSet<TRSTerm> res = new HashMultiSet<TRSTerm>();
        for (Map.Entry<Multiterm,Integer> entry : from.entrySet()) {
            res.add(entry.getKey().toTerm(), entry.getValue());
        }
        return res;
    }

    /** How do <code>M</code> and <code>N</code> relate in this multiset
     * extension?
     */
    public OrderRelation relate(MultiSet<TRSTerm> M, MultiSet<TRSTerm> N) {
        MultiSet<TRSTerm> Mprime;
        MultiSet<TRSTerm> Nprime;

    if(this.order instanceof RPO) {
        /* by transforming terms into multiterms, terms are considered
         * equal if they differ only by a permutation of arguments */

        MultiSet<Multiterm> MM = MultisetExtension.toMultiterm(M);
        MultiSet<Multiterm> NN = MultisetExtension.toMultiterm(N);

        if(MM.equals(NN)) {
            return OrderRelation.EQ;
        }

        Mprime = MultisetExtension.fromMultiterm(MM.subtract(NN));
        Nprime = MultisetExtension.fromMultiterm(NN.subtract(MM));
    }
    else if(this.order instanceof QRPO) {
        /* by transforming terms into multiterms, terms are considered
         * equal if they are equal according to the status map and qoset*/
        QRPO qrpo = (QRPO)this.order;

        MultiSet<Multiterm> MM = MultisetExtension.toMultiterm(M, (Qoset<FunctionSymbol>) qrpo.getPrecedence());
        MultiSet<Multiterm> NN = MultisetExtension.toMultiterm(N, (Qoset<FunctionSymbol>) qrpo.getPrecedence());

        if(MM.equals(NN)) {
            return OrderRelation.EQ;
        }

        Mprime = MultisetExtension.fromMultiterm(MM.subtract(NN));
        Nprime = MultisetExtension.fromMultiterm(NN.subtract(MM));
    }
    else if(this.order instanceof RPOS) {
        /* by transforming terms into multiterms, terms are considered
         * equal if they are equal according to the status map*/
        RPOS rpos = (RPOS)this.order;

        MultiSet<Multiterm> MM = MultisetExtension.toMultiterm(M, rpos.getStatusMap());
        MultiSet<Multiterm> NN = MultisetExtension.toMultiterm(N, rpos.getStatusMap());

        if(MM.equals(NN)) {
            return OrderRelation.EQ;
        }

        Mprime = MultisetExtension.fromMultiterm(MM.subtract(NN));
        Nprime = MultisetExtension.fromMultiterm(NN.subtract(MM));
    }
    else if(this.order instanceof QRPOS) {
        /* by transforming terms into multiterms, terms are considered
         * equal if they are equal according to the status map*/
        QRPOS qrpos = (QRPOS)this.order;

        MultiSet<Multiterm> MM = MultisetExtension.toMultiterm(M, qrpos.getStatusMap(), (Qoset<FunctionSymbol>)qrpos.getPrecedence());
        MultiSet<Multiterm> NN = MultisetExtension.toMultiterm(N, qrpos.getStatusMap(), (Qoset<FunctionSymbol>)qrpos.getPrecedence());

        if(MM.equals(NN)) {
            return OrderRelation.EQ;
        }

        Mprime = MultisetExtension.fromMultiterm(MM.subtract(NN));
        Nprime = MultisetExtension.fromMultiterm(NN.subtract(MM));
    }
/*    else if(this.order instanceof ACRPOS) {
        /* by transforming terms into multiterms, terms are considered
         * equal if they are equal according to the status map*
        ACRPOS acrpos = (ACRPOS)this.order;

        MultiSet<FlattenedMultiterm> MM = toFlattenedMultiterm(M, acrpos.getStatusMap());
        MultiSet<FlattenedMultiterm> NN = toFlattenedMultiterm(N, acrpos.getStatusMap());

        if(MM.equals(NN)) {
            return Relation.EQ;
        }

        Mprime = fromFlattenedMultiterm(MM.subtract(NN));
        Nprime = fromFlattenedMultiterm(NN.subtract(MM));
    }
    else if(this.order instanceof ACRPOSf) {
        /* by transforming terms into multiterms, terms are considered
         * equal if they are equal according to the status map*
        ACRPOSf acrpos = (ACRPOSf)this.order;

        MultiSet<FlattenedMultiterm> MM = toFlattenedMultiterm(M, acrpos.getStatusMap());
        MultiSet<FlattenedMultiterm> NN = toFlattenedMultiterm(N, acrpos.getStatusMap());

        if(MM.equals(NN)) {
            return Relation.EQ;
        }

        Mprime = fromFlattenedMultiterm(MM.subtract(NN));
        Nprime = fromFlattenedMultiterm(NN.subtract(MM));
    }
    else if(this.order instanceof ACQRPOS) {
        /* by transforming terms into multiterms, terms are considered
         * equal if they are equal according to the status map*
        ACQRPOS acqrpos = (ACQRPOS)this.order;

        MultiSet<FlattenedQuasiMultiterm> MM = toFlattenedQuasiMultiterm(M, acqrpos.getStatusMap(), (Qoset)acqrpos.getPrecedence());
        MultiSet<FlattenedQuasiMultiterm> NN = toFlattenedQuasiMultiterm(N, acqrpos.getStatusMap(), (Qoset)acqrpos.getPrecedence());

        if(MM.equals(NN)) {
            return Relation.EQ;
        }

        Mprime = fromFlattenedQuasiMultiterm(MM.subtract(NN));
        Nprime = fromFlattenedQuasiMultiterm(NN.subtract(MM));
    }
    else if(this.order instanceof ACQRPOSf) {
        /* by transforming terms into multiterms, terms are considered
         * equal if they are equal according to the status map*
        ACQRPOSf acqrpos = (ACQRPOSf)this.order;

        MultiSet<FlattenedQuasiMultiterm> MM = toFlattenedQuasiMultiterm(M, acqrpos.getStatusMap(), (Qoset)acqrpos.getPrecedence());
        MultiSet<FlattenedQuasiMultiterm> NN = toFlattenedQuasiMultiterm(N, acqrpos.getStatusMap(), (Qoset)acqrpos.getPrecedence());

        if(MM.equals(NN)) {
            return Relation.EQ;
        }

        Mprime = fromFlattenedQuasiMultiterm(MM.subtract(NN));
        Nprime = fromFlattenedQuasiMultiterm(NN.subtract(MM));
    }       */
    else {
        //System.err.println("MultisetExtension says: OH NO! I don't know that order!");
        if(M.equals(N)) {
        return OrderRelation.EQ;
        }

        Mprime = M.subtract(N);
        Nprime = N.subtract(M);
    }

    this.left = new HashMultiSet<TRSTerm>(Mprime);
    this.right = new HashMultiSet<TRSTerm>(Nprime);

    MultiSet<TRSTerm> GENGRusable = new HashMultiSet<TRSTerm>(Mprime);

    if(this.calculate(Mprime, Nprime, GENGRusable, Nprime.isEmpty())) {
        return OrderRelation.GR;
    }
    else {
        return OrderRelation.NGE;
    }
    }


    /* We have to make sure that each element from MM is either used for
     * exactly on GENGR comparison or for arbitrary many GE comparisons.
     */
    private boolean calculate(MultiSet<TRSTerm> MM, MultiSet<TRSTerm> NN, MultiSet<TRSTerm> GENGRusable, boolean hasStrict) {
    if(NN.isEmpty()) {
        return hasStrict || !GENGRusable.isEmpty();
    }
    else {
        MultiSet<TRSTerm> newNN = new HashMultiSet<TRSTerm>(NN);
        TRSTerm t = NN.keySet().iterator().next();
        newNN.removeOne(t);
        boolean res = false;

        Iterator<TRSTerm> e = MM.keySet().iterator();
        while(e.hasNext() && res==false) {
            TRSTerm s = e.next();
        OrderRelation ord = this.order.compare(s, t);
        if(ord == OrderRelation.GR || ((ord == OrderRelation.GENGR || ord == OrderRelation.EQ) && GENGRusable.contains(s))) {
            MultiSet<TRSTerm> newGENGRusable = new HashMultiSet<TRSTerm>(GENGRusable);
            newGENGRusable.removeOne(s);
            MultiSet<TRSTerm> newMM;
            boolean newHasStrict;
            if(ord != OrderRelation.GR) {
            newMM = new HashMultiSet<TRSTerm>(MM);
            newMM.removeOne(s);
            newHasStrict = hasStrict;
            }
            else {
            newMM = new HashMultiSet<TRSTerm>(MM);
            newHasStrict = true;
            }
            res = this.calculate(newMM, newNN, newGENGRusable, newHasStrict);
        }
        }
        return res;
    }
    }

    /** Returns <code>M.subtract(N)</code>.
     */
    public MultiSet<TRSTerm> getLeft() {
    return this.left;
    }

    /** Returns <code>N.subtract(M)</code>.
     */
    public MultiSet<TRSTerm> getRight() {
    return this.right;
    }

    /** Returns a new multiset consisting of the maximal elements w.r.t.
     * the order */
/*
    public MultiSet<Terms maximalElements(MultiSet<Terms M) {
    MultiSet<Terms res = MultiSet<Terms.create();
    Enumeration e1;
    Enumeration e2;
    Term s;
    Term t;
    boolean foundBigger;

    e1 = M.elements();
    while(e1.hasMoreElements()) {
        s = (Term)e1.nextElement();
        foundBigger = false;
        e2 = M.elements();
        while(e2.hasMoreElements() && foundBigger==false) {
        t = (Term)e2.nextElement();
        if(!s.equals(t)) {
            foundBigger = order.inRelation(t, s);
        }
        }
        if(!foundBigger) {
        res.add(s);
        }
    }

    return res;
    }
*/

}
