package aprove.verification.dpframework.Orders;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.DoubleHash;
import aprove.verification.dpframework.Orders.Utility.FlattenedMultiterm;
import aprove.verification.dpframework.Orders.Utility.Multiterm;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/**
 * Implementation of Rubio's fully syntactic ACRPOS.
 * @author Stephan Falke
 * @version $Id$
 */
public class ACRPOS implements ExportableOrder<TRSTerm>, MultisetExtensibleOrder<TRSTerm> {

    final static String orderName = "AC-Compatible Recursive Path Order with Status";

    /**
     * Creates a new instance of <code>ACRPOS</code>.
     * @param precedence   the precedence to be used
     * @param statusMap   the status map to be used
     */
    public static ACRPOS create(Poset<FunctionSymbol> precedence, StatusMap<FunctionSymbol> statusMap) {
        return new ACRPOS(precedence, statusMap);
    }

    /**
     * Creates a new instance of <code>ACRPOS</code>.
     * @param signature   the names of the symbols
     * @param status      the status to be used
     */
    public static ACRPOS create(Status<FunctionSymbol> status) {
        return new ACRPOS(status.getPrecedence(), status.getStatusMap());
    }

    /**
     * Calculates the minimal extensions of <code>status</code> such
     * that <code>s</code> and <code>t</code> are equal as multiterms.
     */
    public static ExtHashSetOfStatuses<FunctionSymbol> minimalEqualizers(
        TRSTerm s,
        TRSTerm t,
        Status<FunctionSymbol> stat,
        boolean lex,
        boolean onlyLR,
        boolean mul,
        boolean flat,
        List Cs
    ) {
        return ACRPOS.minimalExt(s, t, stat, true, lex, onlyLR, mul, flat, Cs);
    }

    /** Calculates the minimal extensions of <code>status</code> such
     * that <code>s >= t</code> is satisfied but not <code>s > t</code>
     */
    public static ExtHashSetOfStatuses<FunctionSymbol> minimalGENGRs(
        TRSTerm s,
        TRSTerm t,
        Status<FunctionSymbol> stat,
        boolean lex,
        boolean onlyLR,
        boolean mul,
        boolean flat,
        List Cs
    ) {
        return ACRPOS.minimalExt(s, t, stat, false, lex, onlyLR, mul, flat, Cs);
    }

    private static ExtHashSetOfStatuses<FunctionSymbol> minimalExt(
        TRSTerm origS,
        TRSTerm origT,
        Status<FunctionSymbol> q,
        boolean eq,
        boolean lex,
        boolean onlyLR,
        boolean mul,
        boolean flat,
        List Cs
    ) {
        ExtHashSetOfStatuses<FunctionSymbol> res = ExtHashSetOfStatuses.create(q.getSet());
        if (Multiterm.create(origS, q.getStatusMap()).equals(Multiterm.create(origT, q.getStatusMap()))) {
            res.add(q);
            return res;
        } else if (origS.isVariable()) {
            if (origT.isVariable() || eq) {
                /* no way! */
                return res;
            } else {
                final TRSFunctionApplication t = (TRSFunctionApplication)origT;
                final FunctionSymbol tSymb = t.getRootSymbol();
                if (tSymb.getArity() == 0) {
                    /* minimal constants are GE to variables */
                    final Status<FunctionSymbol> statusClone = q.deepcopy();
                    boolean result = false;
                    try {
                        statusClone.setMinimal(tSymb);
                        result = true;
                    } catch (StatusException e) {
                        /* that didn't work... */
                    }
                    if (result) {
                        res.add(statusClone);
                    }
                }
                return res;
            }
        } else if (origT.isVariable()) {
            /* no way */
            return res;
        } else {
            final TRSFunctionApplication s = (TRSFunctionApplication)origS;
            final TRSFunctionApplication t = (TRSFunctionApplication)origT;
            /* s = f(s_1, ..., s_n), t = g(t_1, ..., t_m) */
            final FunctionSymbol f = s.getRootSymbol();
            final FunctionSymbol g = t.getRootSymbol();
            if (!f.equals(g)) {
                /* no way! */
                return res;
            }
            if (q.hasPermutation(f)) {
                final Iterator<? extends TRSTerm> i1 = s.getArguments().iterator();
                final Iterator<? extends TRSTerm> i2 = t.getArguments().iterator();
                res.add(q);
                try {
                    while (i1.hasNext() && !res.isEmpty()) {
                        final Status<FunctionSymbol> tmp = res.intersectAll();
                        res =
                            res.mergeAll(
                                ACRPOS.minimalExt(i1.next(), i2.next(), tmp, eq, lex, onlyLR, mul, flat, Cs)
                            ).minimalElements();
                    }
                } catch (StatusException e) {
                    res = ExtHashSetOfStatuses.create(q.getSet());
                }
                return res;
            }
            else if (!q.hasEntry(f)) {
                /* lex */
                final Iterator<? extends TRSTerm> i1 = s.getArguments().iterator();
                final Iterator<? extends TRSTerm> i2 = t.getArguments().iterator();
                res.add(q);
                try {
                    while (i1.hasNext() && !res.isEmpty()) {
                        final Status<FunctionSymbol> tmp = res.intersectAll();
                        res =
                            res.mergeAll(
                                ACRPOS.minimalExt(i1.next(), i2.next(), tmp, eq, lex, onlyLR, mul, flat, Cs)
                            ).minimalElements();
                    }
                } catch (StatusException e) {
                    res = ExtHashSetOfStatuses.create(q.getSet());
                }
                /* multiset */
                if (mul) {
                    final Status<FunctionSymbol> tmp = q.deepcopy();
                    tmp.assignMultisetStatus(f);
                    try {
                        res = res.union(ACRPOS.minimalExt(s, t, tmp, eq, lex, onlyLR, mul, flat, Cs)).minimalElements();
                    } catch (StatusException e) {
                        res = ExtHashSetOfStatuses.create(q.getSet());
                    }
                }
                /* flat */
                if (flat && f.getArity() == 2) {
                    final Status<FunctionSymbol> tmp = q.deepcopy();
                    tmp.assignFlatStatus(f);
                    try {
                        res = res.union(ACRPOS.minimalExt(s, t, tmp, eq, lex, onlyLR, mul, flat, Cs)).minimalElements();
                    } catch (StatusException e) {
                        res = ExtHashSetOfStatuses.create(q.getSet());
                    }
                }
                return res;
            } else if (q.hasFlatStatus(f)) {
                /* flat status */
                final List<TRSTerm> sArgs =
                    FlattenedMultiterm.toTerm(
                        FlattenedMultiterm.create(s, q.getStatusMap()).getMultiArguments()
                    ).toList();
                final List<TRSTerm> tArgs =
                    FlattenedMultiterm.toTerm(
                        FlattenedMultiterm.create(t, q.getStatusMap()).getMultiArguments()
                    ).toList();
                if (sArgs.size() != tArgs.size()) {
                    /* no way! */
                    return res;
                }
                final DoubleHash<TRSTerm, TRSTerm, ExtHashSetOfStatuses<FunctionSymbol>> dh = DoubleHash.create();
                final Iterator<?> i = sArgs.iterator();
                Iterator<?> j;
                while (i.hasNext()) {
                    final TRSTerm newLeft = (TRSTerm)i.next();
                    j = tArgs.iterator();
                    while (j.hasNext()) {
                        final TRSTerm newRight = (TRSTerm)j.next();
                        dh.put(
                            newLeft,
                            newRight,
                            ACRPOS.minimalExt(newLeft, newRight, q, eq, lex, onlyLR, mul, flat, Cs)
                        );
                    }
                }
                for (Permutation p : PermutationGenerator.create(sArgs.size())) {
                    ExtHashSetOfStatuses<FunctionSymbol> tmpres = ExtHashSetOfStatuses.create(q.getSet());
                    tmpres.add(q);
                    try {
                        for (int k = 0; k < sArgs.size(); k++) {
                            tmpres = tmpres.mergeAll(dh.get(sArgs.get(k), tArgs.get(p.get(k)))).minimalElements();
                        }
                        res = res.union(tmpres).minimalElements();
                    } catch (StatusException excep) {
                        res = ExtHashSetOfStatuses.create(q.getSet());
                    }
                }
                return res;
            }
            else if (q.hasMultisetStatus(f)) {
                /* multiset */
                final DoubleHash<TRSTerm, TRSTerm, ExtHashSetOfStatuses<FunctionSymbol>> dh = DoubleHash.create();
                for (TRSTerm s_i : s.getArguments()) {
                    for (TRSTerm t_j : t.getArguments()) {
                        dh.put(s_i, t_j, ACRPOS.minimalExt(s_i, t_j, q, eq, lex, onlyLR, mul, flat, Cs));
                    }
                }
                for (Permutation p : PermutationGenerator.create(f.getArity())) {
                    ExtHashSetOfStatuses<FunctionSymbol> tmpres = ExtHashSetOfStatuses.create(q.getSet());
                    tmpres.add(q);
                    try {
                        for (int i = 0; i < p.size(); i++) {
                            tmpres =
                                tmpres.mergeAll(dh.get(s.getArgument(i), t.getArgument(p.get(i)))).minimalElements();
                        }
                        res = res.union(tmpres).minimalElements();
                    } catch (StatusException e) {
                        res = ExtHashSetOfStatuses.create(q.getSet());
                    }
                }
                return res;
            }
            return res;
        }
    }

    private final EMB emb;

    private final HashOrder ho;

    private final Poset<FunctionSymbol> precedence;

    private final StatusMap<FunctionSymbol> statusMap;

    private ACRPOS(Poset<FunctionSymbol> precedence, StatusMap<FunctionSymbol> statusMap) {
        this.precedence = precedence;
        this.statusMap = statusMap;
        this.ho = HashOrder.createHO();
        this.emb = EMB.create();
    }

    /**
     * @return <code>true</code> is <code>s</code> and <code>t</code> are equal as flattend multiterms.
     */
    @Override
    public boolean areEquivalent(TRSTerm s, TRSTerm t) {
        return FlattenedMultiterm.create(s, this.statusMap).equals(FlattenedMultiterm.create(t, this.statusMap));
    }

    @Override
    public OrderRelation compare(TRSTerm s, TRSTerm t) {
        return this.calculate(s, t);
    }

    @Override
    public String export(Export_Util eu) {
        return
            "AC-recursive path order with status "
            + eu.cite(Citation.ACRPOS)
            + "."
            + eu.linebreak()
            + Status.create(this.precedence, this.statusMap).export(eu);
    }

    /**
     * @return The used precedence.
     */
    public OrderedSet<FunctionSymbol> getPrecedence() {
        return this.precedence;
    }

    /**
     * @return The used status map.
     */
    public StatusMap getStatusMap() {
        return this.statusMap;
    }

    @Override
    public boolean inRelation(TRSTerm s, TRSTerm t) {
        this.calculate(s, t);
        return (this.ho.get(s, t) == OrderRelation.GR);
    }

    @Override
    public String isCPFSupported() {
        return this.getClass().getCanonicalName();
    }

    @Override
    public boolean solves(Constraint<TRSTerm> c) {
        final OrderRelation res = this.calculate(c.getLeft(), c.getRight());
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
    public Element toCPF(Document doc, XMLMetaData xmlMetaData) {
        throw new RuntimeException("no CPF export " + this.isCPFSupported());
    }

    public String toHTML() {
        return Status.create(this.precedence, this.statusMap).toHTML();
    }

    @Override
    public String toString() {
        return Status.create(this.precedence, this.statusMap).toString();
    }

    /**
     * We build a hashtble with the results of comparing the relevant subterms of s and t.
     */
    private OrderRelation calculate(TRSTerm origS, TRSTerm origT) {
        boolean result = false;
        OrderRelation res;
        res = this.ho.get(origS, origT);
        if (res != null) {
            /* we already know it */
            return res;
        } else {
            if (this.emb.inRelation(origS, origT)) {
                this.ho.put(origS, origT, OrderRelation.GR);
                this.ho.put(origT, origS, OrderRelation.NGE);
                return OrderRelation.GR;
            }
            /* we don't know about s and t yet */
            if (
                FlattenedMultiterm.create(
                    origS,
                    this.statusMap
                ).equals(FlattenedMultiterm.create(origT, this.statusMap))
            ) {
                /* they are equal */
                this.ho.put(origS, origT, OrderRelation.EQ);
                return OrderRelation.EQ;
            } else if (origS.isVariable()) {
                result = this.isGENGR(origS, origT);
                if (result) {
                    this.ho.put(origS, origT, OrderRelation.GENGR);
                    return OrderRelation.GENGR;
                } else {
                    this.ho.put(origS, origT, OrderRelation.NGE);
                    return OrderRelation.NGE;
                }
            } else {
                final TRSFunctionApplication s = (TRSFunctionApplication)origS;
                /* s = f(s_1), ..., s_n) */
                if (origT.isVariable()) {
                    result = s.getVariables().contains(origT);
                } else {
                    final TRSFunctionApplication t = (TRSFunctionApplication)origT;
                    /* t = g(t_1, ..., t_m) */
                    Iterator<?> i;
                    Iterator<?> j;
                    final FunctionSymbol symbLeft = s.getRootSymbol();
                    final FunctionSymbol symbRight = t.getRootSymbol();
                    TRSTerm s_i;
                    TRSTerm t_i;
                    if (symbLeft.equals(symbRight) && symbLeft.getArity() == 1) {
                        res = this.calculate(s.getArgument(0), t.getArgument(0));
                        result = (res == OrderRelation.GR);
                    } else if (symbLeft.equals(symbRight) && this.statusMap.hasPermutation(symbLeft)) {
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
                        while (i.hasNext() && (res == OrderRelation.EQ || res == OrderRelation.GENGR)) {
                            s_i = (TRSTerm)i.next();
                            t_i = (TRSTerm)j.next();
                            res = this.calculate(s_i, t_i);
                        }
                        if (!i.hasNext() && (res == OrderRelation.EQ || res == OrderRelation.GENGR)) {
                            /* out of arguments */
                            this.ho.put(s, t, OrderRelation.GENGR);
                            return OrderRelation.GENGR;
                        }
                        /* now, s_i != t_i */
                        res = this.calculate(s_i, t_i);
                        if (res == OrderRelation.GR) {
                            /* s_i GR t_i */
                            /* continue (2b), no need to do (2a) */
                            /* s_i GR t_i ==> s GR t_i */
                            this.ho.put(s, t_i, OrderRelation.GR);
                            this.ho.put(t_i, s, OrderRelation.NGE);
                            result = true;
                            while (j.hasNext() && result == true) {
                                t_i = (TRSTerm)j.next();
                                res = this.calculate(s, t_i);
                                if (res != OrderRelation.GR) {
                                    if (res == OrderRelation.EQ) {
                                        /* s EQ t_i ==> t GR s */
                                        this.ho.put(t, s, OrderRelation.GR);
                                    }
                                    result = false;
                                }
                            }
                        } else {
                            /* s_i NGE t_i */
                            /* check (2a) for s_i+1, ..., s_n */
                            result = false;
                            while (i.hasNext() && result == false) {
                                s_i = (TRSTerm)i.next();
                                res = this.calculate(s_i, t);
                                if (res == OrderRelation.EQ || res == OrderRelation.GR || res == OrderRelation.GENGR) {
                                    result = true;
                                }
                            }
                        }
                    } else if (symbLeft.equals(symbRight)
                        && this.statusMap.hasMultisetStatus(symbLeft)) {
                        /* (2d) */
                        final MultiSet<TRSTerm> S = new HashMultiSet<TRSTerm>(s.getArguments());
                        final MultiSet<TRSTerm> T = new HashMultiSet<TRSTerm>(t.getArguments());
                        final MultisetExtension mul = MultisetExtension.create(this);
                        result = mul.relate(S, T) == OrderRelation.GR;
                    } else if (symbLeft.equals(symbRight)
                        && this.statusMap.hasFlatStatus(symbLeft)) {
                        /* s' >= t for some s' from EmbNoBig(s)? */
                        final FlattenedMultiterm sf = FlattenedMultiterm.create(s, this.statusMap);
                        final FlattenedMultiterm tf = FlattenedMultiterm.create(t, this.statusMap);
                        Set<FlattenedMultiterm> enb = sf.embNoBig(this.precedence);
                        i = enb.iterator();
                        while (i.hasNext() && result == false) {
                            s_i = ((FlattenedMultiterm)i.next()).toTerm();
                            res = this.calculate(s_i, t);
                            if (res == OrderRelation.EQ || res == OrderRelation.GR || res == OrderRelation.GENGR) {
                                result = true;
                            }
                        }
                        if (!result) {
                            /* Oh yeah! */
                            /* s > t' for all t' from EmbNoBig(t)? */
                            enb = tf.embNoBig(this.precedence);
                            i = enb.iterator();
                            result = true;
                            while (i.hasNext() && result) {
                                t_i = ((FlattenedMultiterm)i.next()).toTerm();
                                res = this.calculate(s, t_i);
                                if (res != OrderRelation.GR) {
                                    result = false;
                                }
                            }
                            if (result) {
                                /* NoSmallHead(s) >>=_{pf} NoSmallHead(t)? */
                                final MultiSet<TRSTerm> snsh =
                                    new HashMultiSet<TRSTerm>(
                                        FlattenedMultiterm.toTerm(sf.noSmallHead(this.precedence))
                                    );
                                final MultiSet<TRSTerm> tnsh =
                                    new HashMultiSet<TRSTerm>(
                                        FlattenedMultiterm.toTerm(tf.noSmallHead(this.precedence))
                                    );
                                final MultisetExtension mul = MultisetExtension.create(new ACRPOSf(this, symbLeft));
                                res = mul.relate(snsh, tnsh);
                                result = (res == OrderRelation.EQ || res == OrderRelation.GR);
                            }
                            if (result) {
                                /* either BigHead(s) >> BigHead(t)? */
                                final MultiSet<TRSTerm> sbh =
                                    new HashMultiSet<TRSTerm>(FlattenedMultiterm.toTerm(sf.bigHead(this.precedence)));
                                final MultiSet<TRSTerm> tbh =
                                    new HashMultiSet<TRSTerm>(FlattenedMultiterm.toTerm(tf.bigHead(this.precedence)));
                                MultisetExtension mul = MultisetExtension.create(this);
                                result = mul.relate(sbh, tbh) == OrderRelation.GR;
                                if (!result) {
                                    final SymbolicPolynomial sp = SymbolicPolynomial.createSymbolicPolynomial(sf);
                                    final SymbolicPolynomial tp = SymbolicPolynomial.createSymbolicPolynomial(tf);
                                    final OrderRelation cmp = sp.compareToPositive(tp);
                                    if (cmp == OrderRelation.GR) {
                                        /* or #(s) > #(t) */
                                        result = true;
                                    } else if (cmp == OrderRelation.GE) {
                                        /* or #(s) > #(t) and {s_1,...,s_n} >> {t_1,...,t_m} */
                                        final MultiSet<TRSTerm> S =
                                            new HashMultiSet<TRSTerm>(
                                                FlattenedMultiterm.toTerm(sf.getMultiArguments()).toList()
                                            );
                                        final MultiSet<TRSTerm> T =
                                            new HashMultiSet<TRSTerm>(
                                                FlattenedMultiterm.toTerm(tf.getMultiArguments()).toList()
                                            );
                                        mul = MultisetExtension.create(this);
                                        result = mul.relate(S, T) == OrderRelation.GR;
                                    }
                                }
                            }
                        }
                        if (!result) {
                            /* (2a) */
                            final Iterator<FlattenedMultiterm> e = sf.getMultiArguments().keySet().iterator();
                            while (e.hasNext() && !result) {
                                final TRSTerm sub = e.next().toTerm();
                                res = this.calculate(sub, t);
                                if (res == OrderRelation.GR || res == OrderRelation.EQ || res == OrderRelation.GENGR) {
                                    result = true;
                                }
                            }
                        }
                    } else if (this.precedence.isGreater(symbLeft, symbRight)) {
                        /* f | g */
                        /* (2c), no need for (2a) in this case */
                        if (this.statusMap.hasFlatStatus(symbRight)) {
                            final Set<FlattenedMultiterm> mSet =
                                FlattenedMultiterm.create(t, this.statusMap).getMultiArguments().keySet();
                            final Set<TRSTerm> tSet = new LinkedHashSet<TRSTerm>();
                            for (FlattenedMultiterm mt : mSet) {
                                tSet.add(mt.toTerm());
                            }
                            j = tSet.iterator();
                        } else {
                            j = t.getArguments().iterator();
                        }
                        result = true;
                        while (j.hasNext() && result == true) {
                            t_i = (TRSTerm)j.next();
                            res = this.calculate(s, t_i);
                            if (res != OrderRelation.GR) {
                                if (res == OrderRelation.EQ) {
                                    /* s EQ t_j ==> t GR s */
                                    this.ho.put(t, s, OrderRelation.GR);
                                }
                                result = false;
                            }
                        }
                    } else {
                        /* f and g are incomparable or g | f
                         * or no statuses.
                         * We can only hope for (2a) */
                        if (this.statusMap.hasFlatStatus(symbLeft)) {
                            i = FlattenedMultiterm.create(s, this.statusMap).getMultiArguments().keySet().iterator();
                        } else {
                            i = s.getArguments().iterator();
                        }
                        result = false;
                        while (i.hasNext() && result == false) {
                            final Object o = i.next();
                            if (o instanceof TRSTerm) {
                                s_i = (TRSTerm)o;
                            } else {
                                s_i = ((FlattenedMultiterm)o).toTerm();
                            }
                            res = this.calculate(s_i, t);
                            if (res == OrderRelation.EQ || res == OrderRelation.GR || res == OrderRelation.GENGR) {
                                result = true;
                            }
                        }
                    }
                }
                /* update the hashtable */
                if (result == true) {
                    this.ho.put(s, origT, OrderRelation.GR);
                    this.ho.put(origT, s, OrderRelation.NGE);
                    return OrderRelation.GR;
                } else {
                    result = this.isGENGR(s, origT);
                    if (result) {
                        this.ho.put(s, origT, OrderRelation.GENGR);
                        return OrderRelation.GENGR;
                    } else {
                        this.ho.put(s, origT, OrderRelation.NGE);
                        return OrderRelation.NGE;
                    }
                }
            }
        }
    }

    private boolean isGENGR(TRSTerm origS, TRSTerm origT) {
        if (FlattenedMultiterm.create(origS, this.statusMap).equals(FlattenedMultiterm.create(origT, this.statusMap))) {
            return true;
        } else if (origS.isVariable()) {
            if (origT.isVariable()) {
                /* no way! */
                return false;
            } else {
                final TRSFunctionApplication t = (TRSFunctionApplication)origT;
                final FunctionSymbol tSymb = t.getRootSymbol();
                if (tSymb.getArity() == 0) {
                    /* minimal constants are GE to variables */
                    return this.precedence.isMinimal(tSymb);
                }
                return false;
            }
        } else if (origT.isVariable()) {
            /* no way */
            return false;
        } else {
            final TRSFunctionApplication s = (TRSFunctionApplication)origS;
            final TRSFunctionApplication t = (TRSFunctionApplication)origT;
            /* s = f(s_1, ..., s_n), t = g(t_1, ..., t_m) */
            final FunctionSymbol f = s.getRootSymbol();
            final FunctionSymbol g = t.getRootSymbol();
            if (!f.equals(g)) {
                /* no way! */
                return false;
            }
            if (this.statusMap.hasPermutation(f) || !this.statusMap.hasEntry(f)) {
                final Iterator<?> i1 = s.getArguments().iterator();
                final Iterator<?> i2 = t.getArguments().iterator();
                boolean result = true;
                while (i1.hasNext() && result) {
                    result = this.isGENGR((TRSTerm)i1.next(), (TRSTerm)i2.next());
                }
                return result;
            } else if (this.statusMap.hasFlatStatus(f)) {
                /* AC status */
                final DoubleHash<TRSTerm, TRSTerm, Boolean> dh = DoubleHash.create();
                TRSTerm newLeft;
                TRSTerm newRight;
                final List<TRSTerm> sArgs =
                    FlattenedMultiterm.toTerm(
                        FlattenedMultiterm.create(s, this.statusMap).getMultiArguments()
                    ).toList();
                final List<TRSTerm> tArgs =
                    FlattenedMultiterm.toTerm(
                        FlattenedMultiterm.create(t, this.statusMap).getMultiArguments()
                    ).toList();
                if (sArgs.size() != tArgs.size()) {
                    return false;
                }
                final Iterator<TRSTerm> i = sArgs.iterator();
                Iterator<TRSTerm> j;
                while (i.hasNext()) {
                    newLeft = i.next();
                    j = tArgs.iterator();
                    while (j.hasNext()) {
                        newRight = j.next();
                        dh.put(newLeft, newRight, Boolean.valueOf(this.isGENGR(newLeft, newRight)));
                    }
                }
                final int n = sArgs.size();
                boolean result = false;
                for (Permutation perm : PermutationGenerator.create(n)) {
                    int index = 0;
                    result = true;
                    while (index < n && result) {
                        result = dh.get(sArgs.get(index), tArgs.get(perm.get(index)));
                        index++;
                    }
                    if (result) {
                        break;
                    }
                }
                return result;
            } else {
                /* multiset status */
                final DoubleHash<TRSTerm, TRSTerm, Boolean> dh = DoubleHash.create();
                TRSTerm newLeft;
                TRSTerm newRight;
                Iterator<? extends TRSTerm> i = s.getArguments().iterator();
                Iterator<? extends TRSTerm> j;
                while (i.hasNext()) {
                    newLeft = i.next();
                    j = t.getArguments().iterator();
                    while (j.hasNext()) {
                        newRight = j.next();
                        dh.put(newLeft, newRight, Boolean.valueOf(this.isGENGR(newLeft, newRight)));
                    }
                }
                boolean result = false;
                for (Permutation perm : PermutationGenerator.create(f.getArity())) {
                    i = s.getArguments().iterator();
                    final TRSFunctionApplication newNewRight = LPOS.permuteTerm(t, perm);
                    j = newNewRight.getArguments().iterator();
                    result = true;
                    while (i.hasNext() && result) {
                        result = dh.get(i.next(), j.next());
                    }
                    if (result) {
                        break;
                    }
                }
                return result;
            }
        }
    }

}
