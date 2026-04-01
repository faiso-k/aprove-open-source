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

/** Implementation of the Recursive Path Order with Status and
 * equivalence of distinct function symbols.
 * <p>
 *  Decides whether <code>s</code> > <code>t</code> in this QRPOS
 *  using time O(|<code>s</code>|*|<code>t</code>|).
 *
 *  @author      Stephan Falke
 *  @version $Id$
 */

public class QRPOS extends AbstractQuasiPO implements MultisetExtensibleOrder<TRSTerm> {

    final static String orderName = "Recursive Path Order with Status and Non-Strict Precedence";

    private final HashOrder ho;


    /* constructors */

    private QRPOS(final Qoset<FunctionSymbol> precedence, final StatusMap<FunctionSymbol> statusMap) {
        this.precedence = precedence;
        this.statusMap = statusMap;
        this.ho = HashOrder.createHO();
    }


    /** Creates a new instance of <code>QRPOS</code>.
     * @param precedence   the precedence to be used
     * @param statusMap   the status map to be used
     */
    public static QRPOS create(final Qoset<FunctionSymbol> precedence, final StatusMap<FunctionSymbol> statusMap) {
        return new QRPOS(precedence, statusMap);
    }

    /** Creates a new instance of <code>QRPOS</code>.
     * @param status      the status to be used
     */
    public static QRPOS create(final QuasiStatus<FunctionSymbol> status) {
        return new QRPOS(status.getPrecedence(), status.getStatusMap());
    }

    /** Calculates the minimal extensions of <code>q</code> such that
     * <code>s</code> and <code>t</code> are quasi-equal.
     * @param s   a term
     * @param t   another term
     * @param q   a quasi status
     * @param eq  a collection specifying which function symbols are allowed
     *            to be equivalent, <code>null</code> if there are no such
     *            restrictions
     */
    public static ExtHashSetOfQuasiStatuses<FunctionSymbol> minimalEqualizers(final TRSTerm s, final TRSTerm t, final QuasiStatus<FunctionSymbol> q, final Collection<Doubleton<FunctionSymbol>> eq) {
        return QRPOS.minimalExt(s, t, q, eq, true);
    }

    /** Calculates the minimal extensions of <code>q</code> such that
     * <code>s >= t</code> is satisfied but not <code>s > t</code>.
     * @param s   a term
     * @param t   another term
     * @param q   a quasi status
     * @param eq  a collection specifying which function symbols are allowed
     *            to be equivalent, <code>null</code> if there are no such
     *            restrictions
     */
    public static ExtHashSetOfQuasiStatuses<FunctionSymbol> minimalGENGRs(final TRSTerm s, final TRSTerm t, final QuasiStatus<FunctionSymbol> q, final Collection<Doubleton<FunctionSymbol>> eq) {
        return QRPOS.minimalExt(s, t, q, eq, false);
    }

    private static ExtHashSetOfQuasiStatuses<FunctionSymbol> minimalExt(final TRSTerm origS, final TRSTerm origT, final QuasiStatus<FunctionSymbol> q, final Collection<Doubleton<FunctionSymbol>> eq, final boolean equal) {
        ExtHashSetOfQuasiStatuses<FunctionSymbol> res = ExtHashSetOfQuasiStatuses.create(q.getSet());
        if(Multiterm.create(origS, q.getStatusMap(), q.getPrecedence()).equals(Multiterm.create(origT, q.getStatusMap(), q.getPrecedence()))) {
            res.add(q);
            return res;
        }
        else if(origS.isVariable()) {
            if(origT.isVariable() || equal) {
                /* no way! */
                return res;
            }
            else {
                final TRSFunctionApplication t = (TRSFunctionApplication)origT;
                final FunctionSymbol tSymb = t.getRootSymbol();
                if(tSymb.getArity()==0) {
                    /* minimal constants are GE to variables */
                    final QuasiStatus<FunctionSymbol> statusClone = q.deepcopy();
                    boolean result = false;
                    try {
                        statusClone.setMinimal(tSymb);
                        result = true;
                    }
                    catch(final QuasiStatusException e) {
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
            if(f.getArity() != g.getArity()) {
                /* m != n, no way! */
                return res;
            }
            if((f.equals(g) || q.areEquivalent(f, g))
                    && f.getArity()==1 && g.getArity()==1) {
                return QRPOS.minimalExt(s.getArgument(0), t.getArgument(0), q, eq, equal);
            }
            if(f.equals(g)) {
                if(q.hasPermutation(f)) {
                    final Iterator i1 = s.getArguments().iterator();
                    final Iterator i2 = t.getArguments().iterator();
                    res.add(q);
                    try {
                        while(i1.hasNext() && !res.isEmpty()) {
                            final QuasiStatus<FunctionSymbol> tmp = res.intersectAll();
                            res = res.mergeAll(QRPOS.minimalExt((TRSTerm)i1.next(), (TRSTerm)i2.next(), tmp, eq, equal)).minimalElements();
                        }
                    }
                    catch(final QuasiStatusException e) {
                        res = ExtHashSetOfQuasiStatuses.create(q.getSet());
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
                            final QuasiStatus<FunctionSymbol> tmp = res.intersectAll();
                            res = res.mergeAll(QRPOS.minimalExt((TRSTerm)i1.next(), (TRSTerm)i2.next(), tmp, eq, equal)).minimalElements();
                        }
                    }
                    catch(final QuasiStatusException e) {
                        res = ExtHashSetOfQuasiStatuses.create(q.getSet());
                    }

                    /* multiset */
                    final QuasiStatus<FunctionSymbol> tmp = q.deepcopy();
                    tmp.assignMultisetStatus(f);
                    try {
                        res = res.union(QRPOS.minimalExt(s, t, tmp, eq, equal)).minimalElements();
                    }
                    catch(final QuasiStatusException e) {
                        res = ExtHashSetOfQuasiStatuses.create(q.getSet());
                    }

                    return res;
                }
                else if(q.hasMultisetStatus(f)) {
                    Iterator i1;
                    Iterator i2;

                    final DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfQuasiStatuses<FunctionSymbol>> dh = DoubleHash.create();
                    i1 = s.getArguments().iterator();
                    while(i1.hasNext()) {
                        final TRSTerm s_i = (TRSTerm)i1.next();
                        i2 = t.getArguments().iterator();
                        while(i2.hasNext()) {
                            final TRSTerm t_j = (TRSTerm)i2.next();
                            dh.put(s_i, t_j, QRPOS.minimalExt(s_i, t_j, q, eq, equal));
                        }
                    }

                    for (final Permutation p : PermutationGenerator.create(f.getArity())) {
                        ExtHashSetOfQuasiStatuses<FunctionSymbol> tmpres = ExtHashSetOfQuasiStatuses.create(q.getSet());
                        tmpres.add(q);
                        try {
                            for(int i=0; i<p.size(); i++) {
                                tmpres = tmpres.mergeAll(dh.get(s.getArgument(i), t.getArgument(p.get(i)))).minimalElements();
                            }
                            res = res.union(tmpres).minimalElements();
                        }
                        catch(final QuasiStatusException e) {
                            res = ExtHashSetOfQuasiStatuses.create(q.getSet());
                        }
                    }

                    return res;
                }
            }
            else if(q.areEquivalent(f, g)) {
                if(q.hasPermutation(f) && q.hasPermutation(g)) {
                    final TRSTerm permS = LPOS.permuteTerm(s, q.getPermutation(f));
                    final TRSTerm permT = LPOS.permuteTerm(t, q.getPermutation(g));
                    final Iterator i1 = ((TRSFunctionApplication)permS).getArguments().iterator();
                    final Iterator i2 = ((TRSFunctionApplication)permT).getArguments().iterator();
                    res.add(q);
                    try {
                        while(i1.hasNext() && !res.isEmpty()) {
                            final QuasiStatus<FunctionSymbol> tmp = res.intersectAll();
                            res = res.mergeAll(QRPOS.minimalExt((TRSTerm)i1.next(), (TRSTerm)i2.next(), tmp, eq, equal)).minimalElements();
                        }
                    }
                    catch(final QuasiStatusException e) {
                        res = ExtHashSetOfQuasiStatuses.create(q.getSet());
                    }

                    return res;
                }
                else if(q.hasMultisetStatus(f) && q.hasMultisetStatus(g)) {
                    Iterator i1;
                    Iterator i2;

                    final DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfQuasiStatuses<FunctionSymbol>> dh = DoubleHash.create();
                    i1 = s.getArguments().iterator();
                    while(i1.hasNext()) {
                        final TRSTerm s_i = (TRSTerm)i1.next();
                        i2 = t.getArguments().iterator();
                        while(i2.hasNext()) {
                            final TRSTerm t_j = (TRSTerm)i2.next();
                            dh.put(s_i, t_j, QRPOS.minimalExt(s_i, t_j, q, eq, equal));
                        }
                    }

                    for (final Permutation p : PermutationGenerator.create(f.getArity())) {
                        ExtHashSetOfQuasiStatuses<FunctionSymbol> tmpres = ExtHashSetOfQuasiStatuses.create(q.getSet());
                        tmpres.add(q);
                        try {
                            for(int i=0; i<p.size(); i++) {
                                tmpres = tmpres.mergeAll(dh.get(s.getArgument(i), t.getArgument(p.get(i)))).minimalElements();
                            }
                            res = res.union(tmpres).minimalElements();
                        }
                        catch(final QuasiStatusException e) {
                            res = ExtHashSetOfQuasiStatuses.create(q.getSet());
                        }
                    }

                    return res;
                }
                else {
                    Iterator l;
                    Iterator r;

                    final DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfQuasiStatuses<FunctionSymbol>> dh = DoubleHash.create();
                    l = s.getArguments().iterator();
                    while(l.hasNext()) {
                        final TRSTerm s_i = (TRSTerm)l.next();
                        r = t.getArguments().iterator();
                        while(r.hasNext()) {
                            final TRSTerm t_j = (TRSTerm)r.next();
                            dh.put(s_i, t_j, QRPOS.minimalExt(s_i, t_j, q, eq, equal));
                        }
                    }

                    /* permutation variants */
                    Iterable<Permutation> i1;
                    Iterable<Permutation> i2;
                    List<Permutation> left = null;
                    List<Permutation> right = null;
                    if(q.hasPermutation(f)) {
                        left = new ArrayList<Permutation>();
                        left.add(q.getPermutation(f));
                        i1 = left;
                    }
                    else {
                        i1 = PermutationGenerator.create(f.getArity());
                    }
                    if(f.equals(g) || q.hasPermutation(g)) {
                        right = new ArrayList<Permutation>();
                        if(q.hasPermutation(g)) {
                            right.add(q.getPermutation(g));
                        }
                    }

                    for (final Permutation pLeft : i1) {

                        if(f.equals(g)) {
                            right.clear();
                            right.add(pLeft);
                            i2 = right;
                        }
                        else if(q.hasPermutation(g)) {
                            i2 = right;
                        }
                        else {
                            i2 = PermutationGenerator.create(g.getArity());
                        }

                        for (final Permutation pRight : i2) {
                            final TRSTerm permS = LPOS.permuteTerm(s, pLeft);
                            final TRSTerm permT = LPOS.permuteTerm(t, pRight);
                            final QuasiStatus<FunctionSymbol> tmp = q.deepcopy();
                            tmp.assignPermutation(f, pLeft);
                            tmp.assignPermutation(g, pRight);
                            ExtHashSetOfQuasiStatuses<FunctionSymbol> tmpres = ExtHashSetOfQuasiStatuses.create(q.getSet());
                            tmpres.add(tmp);
                            final Iterator i = ((TRSFunctionApplication)permS).getArguments().iterator();
                            final Iterator j = ((TRSFunctionApplication)permT).getArguments().iterator();
                            try {
                                while(i.hasNext()) {
                                    tmpres = tmpres.mergeAll(dh.get((TRSTerm)i.next(), (TRSTerm)j.next())).minimalElements();
                                }
                                res = res.union(tmpres).minimalElements();
                            }
                            catch(final QuasiStatusException e) {
                                res = ExtHashSetOfQuasiStatuses.create(q.getSet());
                            }
                        }
                    }

                    /* multiset status */
                    if(!q.hasPermutation(f) && !q.hasPermutation(g)) {
                        final QuasiStatus<FunctionSymbol> tmp = q.deepcopy();
                        tmp.assignMultisetStatus(f);
                        tmp.assignMultisetStatus(g);

                        try {
                            res = res.union(QRPOS.minimalExt(s, t, tmp, eq, equal)).minimalElements();
                        }
                        catch(final QuasiStatusException e) {
                            res = ExtHashSetOfQuasiStatuses.create(q.getSet());
                        }
                    }

                    return res;
                }
            }
            if(!f.equals(g) && !q.areEquivalent(f, g)
                    && (eq==null || eq.contains(Doubleton.create(f, g)))) {
                final QuasiStatus<FunctionSymbol> tmp = q.deepcopy();
                try {
                    tmp.setEquivalent(f, g);
                    res = QRPOS.minimalExt(s, t, tmp, eq, equal);
                }
                catch(final QuasiStatusException e) {
                    /* empty equalizer */
                }

                return res;
            }

            return res;
        }
    }

    private boolean isGENGR(final TRSTerm origS, final TRSTerm origT) {
        if(Multiterm.create(origS, this.statusMap, this.precedence).equals(Multiterm.create(origT, this.statusMap, this.precedence))) {
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
            if(f.getArity() != g.getArity()) {
                /* m != n, no way! */
                return false;
            }
            if((f.equals(g) || this.precedence.areEquivalent(f, g))
                    && f.getArity()==1) {
                return this.isGENGR(s.getArgument(0), t.getArgument(0));
            }
            if(f.equals(g)) {
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
                    /* multiset */
                    Iterator i1;
                    Iterator i2;

                    final DoubleHash<TRSTerm,TRSTerm,Boolean> dh = DoubleHash.create();
                    i1 = s.getArguments().iterator();
                    while(i1.hasNext()) {
                        final TRSTerm s_i = (TRSTerm)i1.next();
                        i2 = t.getArguments().iterator();
                        while(i2.hasNext()) {
                            final TRSTerm t_j = (TRSTerm)i2.next();
                            dh.put(s_i, t_j, Boolean.valueOf(this.isGENGR(s_i, t_j)));
                        }
                    }

                    boolean result = false;
                    for (final Permutation perm : PermutationGenerator.create(f.getArity())) {
                        i1 = s.getArguments().iterator();
                        final TRSTerm newRight = LPOS.permuteTerm(t, perm);
                        i2 = ((TRSFunctionApplication)newRight).getArguments().iterator();
                        result = true;
                        while(i1.hasNext() && result) {
                            result = (dh.get((TRSTerm)i1.next(), (TRSTerm)i2.next())).booleanValue();
                        }
                        if (result) {
                            break;
                        }
                    }
                    return result;
                }
            }
            else if(this.precedence.areEquivalent(f, g)) {
                if(!this.statusMap.hasEntry(f) || !this.statusMap.hasEntry(g)) {
                    return false;
                }
                if(this.statusMap.hasPermutation(f) && this.statusMap.hasPermutation(g)) {
                    final TRSTerm permS = LPOS.permuteTerm(s, this.statusMap.getPermutation(f));
                    final TRSTerm permT = LPOS.permuteTerm(t, this.statusMap.getPermutation(g));
                    final Iterator i1 = ((TRSFunctionApplication)permS).getArguments().iterator();
                    final Iterator i2 = ((TRSFunctionApplication)permT).getArguments().iterator();
                    boolean result = true;
                    while(i1.hasNext() && result) {
                        result = this.isGENGR((TRSTerm)i1.next(), (TRSTerm)i2.next());
                    }

                    return result;
                }
                else if(this.statusMap.hasMultisetStatus(f) && this.statusMap.hasMultisetStatus(g)) {
                    Iterator i1;
                    Iterator i2;

                    final DoubleHash<TRSTerm,TRSTerm,Boolean> dh = DoubleHash.create();
                    i1 = s.getArguments().iterator();
                    while(i1.hasNext()) {
                        final TRSTerm s_i = (TRSTerm)i1.next();
                        i2 = t.getArguments().iterator();
                        while(i2.hasNext()) {
                            final TRSTerm t_j = (TRSTerm)i2.next();
                            dh.put(s_i, t_j, Boolean.valueOf(this.isGENGR(s_i, t_j)));
                        }
                    }

                    boolean result = false;
                    for (final Permutation perm : PermutationGenerator.create(f.getArity())) {
                        i1 = s.getArguments().iterator();
                        final TRSTerm newRight = LPOS.permuteTerm(t, perm);
                        i2 = ((TRSFunctionApplication)newRight).getArguments().iterator();
                        result = true;
                        while(i1.hasNext() && result) {
                            result = (dh.get((TRSTerm)i1.next(), (TRSTerm)i2.next())).booleanValue();
                        }
                        if (result) {
                            break;
                        }
                    }
                    return result;
                }
                else {
                    return false;
                }
            }

            return false;
        }
    }

    /* return 'true' if s>t in the quasi recursive path order,
     * return 'false' otherwise.
     * The lexicographic path order is defined by
     *   s>t  iff  (1) not s=t
     *              and (2a) s=f(s_1, ... ,s_n) and s_j>=t for some 1<=j<=n
     *                   or
     *                  (2b) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_n) and
     *                       there exists an 1<=i<=n such that
     *                       s_p(1) = t_p(1), ... ,s_p(i-1)=t_p(i-1),
     *                       s_p(i)>t_p(i) and s>t_p(j) for all i<j<=n,
     *                       where f and g are equivalent
     *                   or
     *                  (2c) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_m), f|g
     *                       and s>t_i for all 1<=i<=m
     *                   or
     *                  (2d) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_m) and
     *                       {s_1, ... ,s_n} >> {t_1, ... ,t_m} where
     *                       f and g are equivalent
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
     * are equal up to equivalent symbols and permutations of arguments.
     */
    @Override
    public boolean areEquivalent(final TRSTerm s, final TRSTerm t) {
        return Multiterm.create(s, this.statusMap, this.precedence).equals(
                Multiterm.create(t, this.statusMap, this.precedence));
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
            if(Multiterm.create(origS, this.statusMap, this.precedence).equals(
                    Multiterm.create(origT, this.statusMap, this.precedence))) {
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

                    final boolean eq = symbLeft.equals(symbRight) || this.precedence.areEquivalent(symbLeft, symbRight);

                    if(eq && symbLeft.getArity()==1
                            && symbRight.getArity()==1) {
                        res = this.calculate(s.getArgument(0), t.getArgument(0));
                        result = (res==OrderRelation.GR);
                    }
                    else if(eq && symbLeft.getArity()==0) {
                        result = false;
                    }
                    else if(eq && symbRight.getArity()==0) {
                        result = true;
                    }
                    else if(eq && this.statusMap.hasPermutation(symbLeft)
                            && this.statusMap.hasPermutation(symbRight)) {

                        /* apply permutation */
                        final Permutation pS = this.statusMap.getPermutation(symbLeft);
                        final Permutation pT = this.statusMap.getPermutation(symbRight);
                        final TRSTerm permS = LPOS.permuteTerm(s, pS);
                        final TRSTerm permT = LPOS.permuteTerm(t, pT);

                        i = ((TRSFunctionApplication)permS).getArguments().iterator();
                        j = ((TRSFunctionApplication)permT).getArguments().iterator();

                        if(!i.hasNext()) {
                            /* lhs has no arguments, but rhs has */
                            result = false;
                        }
                        else if(!j.hasNext()) {
                            /* rhs has no arguments, but lhs has */
                            result = true;
                        }
                        else {
                            /* arguments on both sides */
                            s_i = (TRSTerm)i.next();
                            t_i = (TRSTerm)j.next();
                            /* skip equal subterms s_i = t_i or s_i >= t_i*/
                            res = this.calculate(s_i, t_i);
                            while(i.hasNext() && j.hasNext() && (res==OrderRelation.EQ || res==OrderRelation.GENGR)) {
                                s_i = (TRSTerm)i.next();
                                t_i = (TRSTerm)j.next();
                                res = this.calculate(s_i, t_i);
                            }

                            if(!i.hasNext() && (res==OrderRelation.EQ || res==OrderRelation.GENGR)) {
                                /* we're out of arguments for s */
                                this.ho.put(t, s, OrderRelation.GR);
                                result = false;
                            }
                            else if(!j.hasNext() && (res==OrderRelation.EQ || res==OrderRelation.GENGR)) {
                                /* out of aguments for t */
                                result = true;
                            }
                            else {
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
                        }
                    }
                    else if(eq && this.statusMap.hasMultisetStatus(symbLeft)
                            && this.statusMap.hasMultisetStatus(symbRight)) {

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

    @Override
    public String toString() {
        return QuasiStatus.create(this.precedence, this.statusMap).toString();
    }


    @Override
    public String export(final Export_Util eu) {
        return "Recursive path order with status "+eu.cite(Citation.RPO)+"."
        +eu.linebreak()+QuasiStatus.create(this.precedence, this.statusMap).export(eu);
    }

}
