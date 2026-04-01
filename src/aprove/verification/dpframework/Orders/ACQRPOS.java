package aprove.verification.dpframework.Orders ;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.DoubleHash;
import aprove.verification.dpframework.Orders.Utility.FlattenedQuasiMultiterm;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/** Implementation of Rubio's fully syntactic ACRPOS with
 * equivalence of distinct function symbols.
 *
 *  @author      Stephan Falke
 *  @version $Id$
 */

public class ACQRPOS implements ExportableOrder<TRSTerm>, MultisetExtensibleOrder<TRSTerm> {

    final static String orderName = "AC-Compatible Recursive Path Order with Status and Non-Strict Precedence";

    private final Qoset<String> precedence;
    private final StatusMap statusMap;
    private final EMB emb;

    private final HashOrder ho;

    /* constructors */

    private ACQRPOS(final Qoset<String> precedence, final StatusMap statusMap) {
    this.precedence = precedence;
    this.statusMap = statusMap;
    this.ho = HashOrder.createHO();
    this.emb = EMB.create();
    }

    /** Creates a new instance of <code>ACQRPOS</code>.
     * @param precedence   the precedence to be used
     * @param statusMap   the status map to be used
     */
    public static ACQRPOS create(final Qoset<String> precedence, final StatusMap statusMap) {
    return new ACQRPOS(precedence, statusMap);
    }

    /** Creates a new instance of <code>ACQRPOS</code>.
     * @param status      the status to be used
     */
    public static ACQRPOS create(final QuasiStatus status) {
    return new ACQRPOS(status.getPrecedence(), status.getStatusMap());
    }

    /** Returns the used precedence.
     */
    public OrderedSet<String> getPrecedence() {
    return this.precedence;
    }

    /** Returns the used status map.
     */
    public StatusMap getStatusMap() {
    return this.statusMap;
    }

    /** Calculates the minimal extensions of <code>q</code> such that
     * <code>s</code> and <code>t</code> are quasi-equal.
     * @param s   a term
     * @param t   another term
     * @param q   a quasi status
     * @param eq  a collection specifying which function symbols are allowed
     *            to be equivalent, <code>null</code> if there are no such
     *            restrictions
     * @param Cs  the names of the C symbols
     */
    public static ExtHashSetOfQuasiStatuses minimalEqualizers(final TRSTerm s, final TRSTerm t, final QuasiStatus q, final Collection<Doubleton<String>> eq, final boolean lex, final boolean onlyLR, final boolean mul, final boolean flat, final List Cs) {
    return ACQRPOS.minimalExt(s, t, q, eq, true, lex, onlyLR, mul, flat, Cs);
    }

    /** Calculates the minimal extensions of <code>q</code> such that
     * <code>s >= t</code> is satisfied but not <code>s > t</code>.
     * @param s   a term
     * @param t   another term
     * @param q   a quasi status
     * @param eq  a collection specifying which function symbols are allowed
     *            to be equivalent, <code>null</code> if there are no such
     *            restrictions
     * @param Cs  the names of the C symbols
     */
    public static ExtHashSetOfQuasiStatuses minimalGENGRs(final TRSTerm s, final TRSTerm t, final QuasiStatus q, final Collection<Doubleton<String>> eq, final boolean lex, final boolean onlyLR, final boolean mul, final boolean flat, final List Cs) {
    return ACQRPOS.minimalExt(s, t, q, eq, false, lex, onlyLR, mul, flat, Cs);
    }

    private static ExtHashSetOfQuasiStatuses minimalExt(final TRSTerm origS, final TRSTerm origT, final QuasiStatus q, final Collection<Doubleton<String>> eq, final boolean equal, final boolean lex, final boolean onlyLR, final boolean mul, final boolean flat, final List Cs) {
    ExtHashSetOfQuasiStatuses res = ExtHashSetOfQuasiStatuses.create(q.getSet());
    if(FlattenedQuasiMultiterm.create(origS, q.getStatusMap(), q.getPrecedence()).equals(FlattenedQuasiMultiterm.create(origT, q.getStatusMap(), q.getPrecedence()))) {
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
            final String tSymbName = tSymb.getName();
            final QuasiStatus statusClone = q.deepcopy();
            boolean result = false;
            try {
            statusClone.setMinimal(tSymbName);
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
        final String fName = f.getName();
        final String gName = g.getName();
        if(f.getArity() != g.getArity()) {
            /* m != n, no way! */
            return res;
        }
        if((fName.equals(gName) || q.areEquivalent(fName, gName))
           && f.getArity()==1 && g.getArity()==1) {
        return ACQRPOS.minimalExt(s.getArgument(0), t.getArgument(0), q, eq, equal, lex, onlyLR, mul, flat, Cs);
        }
            if(fName.equals(gName)) {
        if(q.hasPermutation(fName)) {
            final Iterator i1 = s.getArguments().iterator();
            final Iterator i2 = t.getArguments().iterator();
            res.add(q);
            try {
                while(i1.hasNext() && !res.isEmpty()) {
                final QuasiStatus tmp = res.intersectAll();
                res = res.mergeAll(ACQRPOS.minimalExt((TRSTerm)i1.next(), (TRSTerm)i2.next(), tmp, eq, equal, lex, onlyLR, mul, flat, Cs)).minimalElements();
            }
            }
            catch(final QuasiStatusException e) {
            res = ExtHashSetOfQuasiStatuses.create(q.getSet());
            }

            return res;
        }
        else if(!q.hasEntry(fName)) {
            /* lex */
            final Iterator i1 = s.getArguments().iterator();
            final Iterator i2 = t.getArguments().iterator();
            res.add(q);
            try {
                while(i1.hasNext() && !res.isEmpty()) {
                final QuasiStatus tmp = res.intersectAll();
                res = res.mergeAll(ACQRPOS.minimalExt((TRSTerm)i1.next(), (TRSTerm)i2.next(), tmp, eq, equal, lex, onlyLR, mul, flat, Cs)).minimalElements();
            }
            }
            catch(final QuasiStatusException e) {
            res = ExtHashSetOfQuasiStatuses.create(q.getSet());
            }

            /* multiset */
            if(mul) {
                final QuasiStatus tmp = q.deepcopy();
                tmp.assignMultisetStatus(fName);
                try {
                res = res.union(ACQRPOS.minimalExt(s, t, tmp, eq, equal, lex, onlyLR, mul, flat, Cs)).minimalElements();
                }
                catch(final QuasiStatusException e) {
                res = ExtHashSetOfQuasiStatuses.create(q.getSet());
                }
            }

            /* flat */
            if(flat && f.getArity()==2) {
                final QuasiStatus tmp = q.deepcopy();
                tmp.assignFlatStatus(fName);
                try {
                res = res.union(ACQRPOS.minimalExt(s, t, tmp, eq, equal, lex, onlyLR, mul, flat, Cs)).minimalElements();
                }
                catch(final QuasiStatusException e) {
                res = ExtHashSetOfQuasiStatuses.create(q.getSet());
                }

                return res;
            }
        }
        else if(q.hasMultisetStatus(fName)) {
            Iterator i1;
            Iterator i2;

            final DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfQuasiStatuses> dh = DoubleHash.create();
            i1 = s.getArguments().iterator();
            while(i1.hasNext()) {
            final TRSTerm s_i = (TRSTerm)i1.next();
            i2 = t.getArguments().iterator();
            while(i2.hasNext()) {
                final TRSTerm t_j = (TRSTerm)i2.next();
                dh.put(s_i, t_j, ACQRPOS.minimalExt(s_i, t_j, q, eq, equal, lex, onlyLR, mul, flat, Cs));
            }
            }

            for (final Permutation p : PermutationGenerator.create(f.getArity())) {
            ExtHashSetOfQuasiStatuses tmpres = ExtHashSetOfQuasiStatuses.create(q.getSet());
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
            else if(q.hasFlatStatus(fName)) {
            /* flat status */
            /* collection binary roots of all subterms */
            final FlattenedQuasiMultiterm sflat = FlattenedQuasiMultiterm.create(s, q.getStatusMap(), q.getPrecedence());
            final FlattenedQuasiMultiterm tflat = FlattenedQuasiMultiterm.create(t, q.getStatusMap(), q.getPrecedence());

            final Set<FunctionSymbol> roots = sflat.getReachableCandidates();
            roots.addAll(tflat.getReachableCandidates());

            final List<String> rootsNames = new ArrayList<String>();
            final Iterator it = roots.iterator();
            while(it.hasNext()) {
                final FunctionSymbol symb = (FunctionSymbol)it.next();
                final String name = symb.getName();
                if(eq==null || eq.contains(Doubleton.create(fName, name))) {
                    rootsNames.add(name);
            }
            }

            final int n = rootsNames.size();

            Iterable<Sequence> seq;
            if(n==0) {
            final List<Sequence> sss = new ArrayList<Sequence>(1);
            sss.add(Sequence.create(new int[]{1}));
            seq = sss;
            }
            else {
                seq = SequenceGenerator.create(n, 2);
            }

                    for (final Sequence theSeq : seq) {
                final QuasiStatus tmp = q.deepcopy();
                try {
                    for(int k=0; k<n; k++) {
                    final String name = rootsNames.get(k);
                    if(theSeq.get(k)==1) {
                    tmp.setEquivalent(fName, name);
                    tmp.assignFlatStatus(name);
                }
                }


                    final ArrayList<TRSTerm> sArgs = FlattenedQuasiMultiterm.create(s, tmp.getStatusMap(), tmp.getPrecedence()).getMultiArgumentsAsTermVector();
                    final ArrayList<TRSTerm> tArgs = FlattenedQuasiMultiterm.create(t, tmp.getStatusMap(), tmp.getPrecedence()).getMultiArgumentsAsTermVector();

                    if(sArgs.size()==tArgs.size()) {
                        final DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfQuasiStatuses> dh = DoubleHash.create();
                            final Iterator i = sArgs.iterator();
                                Iterator j;

                            while(i.hasNext()) {
                            final TRSTerm newLeft = (TRSTerm)i.next();
                                j = tArgs.iterator();
                            while(j.hasNext()) {
                                final TRSTerm newRight = (TRSTerm)j.next();
                                dh.put(newLeft, newRight, ACQRPOS.minimalExt(newLeft, newRight, tmp, eq, equal, lex, onlyLR, mul, flat, Cs));
                            }
                            }

                            for (final Permutation p : PermutationGenerator.create(sArgs.size())) {
                            ExtHashSetOfQuasiStatuses tmpres = ExtHashSetOfQuasiStatuses.create(q.getSet());
                            tmpres.add(q);
                            try {
                            for(int k=0; k<sArgs.size(); k++) {
                                tmpres = tmpres.mergeAll(dh.get(sArgs.get(k), tArgs.get(p.get(k)))).minimalElements();
                            }
                            res = res.union(tmpres).minimalElements();
                            }
                            catch(final QuasiStatusException excep) {
                            }
                        }
                }
            }
                catch(final QuasiStatusException e) {
            }
            }

            return res;
            }
        }
        else if(q.areEquivalent(fName, gName)) {
        if(q.hasPermutation(fName) && q.hasPermutation(gName)) {
            final TRSTerm permS = LPOS.permuteTerm(s, q.getPermutation(fName));
            final TRSTerm permT = LPOS.permuteTerm(t, q.getPermutation(gName));
            final Iterator i1 = ((TRSFunctionApplication)permS).getArguments().iterator();
            final Iterator i2 = ((TRSFunctionApplication)permT).getArguments().iterator();
            res.add(q);
            try {
                while(i1.hasNext() && !res.isEmpty()) {
                final QuasiStatus tmp = res.intersectAll();
                res = res.mergeAll(ACQRPOS.minimalExt((TRSTerm)i1.next(), (TRSTerm)i2.next(), tmp, eq, equal, lex, onlyLR, mul, flat, Cs)).minimalElements();
            }
            }
            catch(final QuasiStatusException e) {
            res = ExtHashSetOfQuasiStatuses.create(q.getSet());
            }

            return res;
        }
        else if(q.hasMultisetStatus(fName) && q.hasMultisetStatus(gName)) {
            Iterator i1;
            Iterator i2;

            final DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfQuasiStatuses> dh = DoubleHash.create();
            i1 = s.getArguments().iterator();
            while(i1.hasNext()) {
            final TRSTerm s_i = (TRSTerm)i1.next();
            i2 = t.getArguments().iterator();
            while(i2.hasNext()) {
                final TRSTerm t_j = (TRSTerm)i2.next();
                dh.put(s_i, t_j, ACQRPOS.minimalExt(s_i, t_j, q, eq, equal, lex, onlyLR, mul, flat, Cs));
            }
            }

                    for (final Permutation p : PermutationGenerator.create(f.getArity())) {
            ExtHashSetOfQuasiStatuses tmpres = ExtHashSetOfQuasiStatuses.create(q.getSet());
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
            else if(q.hasFlatStatus(fName) && q.hasFlatStatus(gName)) {
            /* flat status */
            /* collection binary roots of all subterms */
            final FlattenedQuasiMultiterm sflat = FlattenedQuasiMultiterm.create(s, q.getStatusMap(), q.getPrecedence());
            final FlattenedQuasiMultiterm tflat = FlattenedQuasiMultiterm.create(t, q.getStatusMap(), q.getPrecedence());

            final Set<FunctionSymbol> roots = sflat.getReachableCandidates();
            roots.addAll(tflat.getReachableCandidates());

            final List<String> rootsNames = new ArrayList<String>();
            final Iterator<FunctionSymbol> it = roots.iterator();
            while(it.hasNext()) {
                final FunctionSymbol symb = it.next();
                final String name = symb.getName();
                if(eq==null || eq.contains(Doubleton.create(fName, name))) {
                    rootsNames.add(name);
            }
            }

            final int n = rootsNames.size();

            Iterable<Sequence> seq;
            if(n==0) {
            final List<Sequence> sss = new ArrayList<Sequence>(1);
            sss.add(Sequence.create(new int[]{1}));
            seq = sss;
            }
            else {
                seq = SequenceGenerator.create(n, 2);
            }

                    for (final Sequence theSeq : seq) {
                final QuasiStatus tmp = q.deepcopy();
                try {
                    for(int k=0; k<n; k++) {
                    final String name = rootsNames.get(k);
                    if(theSeq.get(k)==1) {
                    tmp.setEquivalent(fName, name);
                    tmp.assignFlatStatus(name);
                }
                }

                    final ArrayList<TRSTerm> sArgs = FlattenedQuasiMultiterm.create(s, tmp.getStatusMap(), tmp.getPrecedence()).getMultiArgumentsAsTermVector();
                            final ArrayList<TRSTerm> tArgs = FlattenedQuasiMultiterm.create(t, tmp.getStatusMap(), tmp.getPrecedence()).getMultiArgumentsAsTermVector();

                    if(sArgs.size()==tArgs.size()) {
                        final DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfQuasiStatuses> dh = DoubleHash.create();
                            final Iterator i = sArgs.iterator();
                                Iterator j;

                            while(i.hasNext()) {
                            final TRSTerm newLeft = (TRSTerm)i.next();
                                j = tArgs.iterator();
                            while(j.hasNext()) {
                                final TRSTerm newRight = (TRSTerm)j.next();
                                dh.put(newLeft, newRight, ACQRPOS.minimalExt(newLeft, newRight, tmp, eq, equal, lex, onlyLR, mul, flat, Cs));
                            }
                            }

                                for (final Permutation p : PermutationGenerator.create(sArgs.size())) {
                            ExtHashSetOfQuasiStatuses tmpres = ExtHashSetOfQuasiStatuses.create(q.getSet());
                            tmpres.add(q);
                            try {
                            for(int k=0; k<sArgs.size(); k++) {
                                tmpres = tmpres.mergeAll(dh.get(sArgs.get(k), tArgs.get(p.get(k)))).minimalElements();
                            }
                            res = res.union(tmpres).minimalElements();
                            }
                            catch(final QuasiStatusException excep) {
                            }
                        }
                }
            }
                catch(final QuasiStatusException e) {
            }
            }

            return res;
            }
        else {
            Iterator l;
            Iterator r;

            final DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfQuasiStatuses> dh = DoubleHash.create();
            l = s.getArguments().iterator();
            while(l.hasNext()) {
            final TRSTerm s_i = (TRSTerm)l.next();
            r = t.getArguments().iterator();
            while(r.hasNext()) {
                final TRSTerm t_j = (TRSTerm)r.next();
                dh.put(s_i, t_j, ACQRPOS.minimalExt(s_i, t_j, q, eq, equal, lex, onlyLR, mul, flat, Cs));
            }
            }

            if(lex && !q.hasMultisetStatus(fName) && !q.hasFlatStatus(fName) &&
               !q.hasMultisetStatus(gName) && !q.hasFlatStatus(gName)
               &&!Cs.contains(fName) && !Cs.contains(gName)) {

                /* permutation variants */
                Iterable<Permutation> i1;
                        Iterable<Permutation> i2;
                List<Permutation> left = null;
                List<Permutation> right = null;
                if(q.hasPermutation(fName)) {
                left = new ArrayList<Permutation>();
                left.add(q.getPermutation(fName));
                i1 = left;
                }
                else {
                if(onlyLR) {
                final List<Permutation> pp = new ArrayList<Permutation>();
                final int[] tmp = new int[f.getArity()];
                for(int i=0; i<f.getArity(); i++) {
                    tmp[i] = i;
                }
                pp.add(Permutation.create(tmp));
                i1 = pp;
                }
                else {
                    i1 = PermutationGenerator.create(f.getArity());
                }
                }
                if(q.hasPermutation(gName)) {
                right = new ArrayList<Permutation>();
                right.add(q.getPermutation(gName));
            }

                for (final Permutation pLeft : i1) {
                if(q.hasPermutation(gName)) {
                    i2 = right;
                }
                else {
                if(onlyLR) {
                    final List<Permutation> pp = new ArrayList<Permutation>();
                    final int[] tmp = new int[g.getArity()];
                    for(int i=0; i<g.getArity(); i++) {
                    tmp[i] = i;
                    }
                    pp.add(Permutation.create(tmp));
                    i2 = pp;
                }
                else {
                        i2 = PermutationGenerator.create(g.getArity());
                }
                }
                for (final Permutation pRight : i2) {
                    final TRSTerm permS = LPOS.permuteTerm(s, pLeft);
                    final TRSTerm permT = LPOS.permuteTerm(t, pRight);
                    final QuasiStatus tmp = q.deepcopy();
                    tmp.assignPermutation(fName, pLeft);
                    tmp.assignPermutation(gName, pRight);
                    ExtHashSetOfQuasiStatuses tmpres = ExtHashSetOfQuasiStatuses.create(q.getSet());
                    tmpres.add(tmp);
                    final Iterator<? extends TRSTerm> i = ((TRSFunctionApplication)permS).getArguments().iterator();
                    final Iterator<? extends TRSTerm> j = ((TRSFunctionApplication)permT).getArguments().iterator();
                    try {
                        while(i.hasNext()) {
                        tmpres = tmpres.mergeAll(dh.get(i.next(), j.next())).minimalElements();
                        }
                        res = res.union(tmpres).minimalElements();
                    }
                    catch(final QuasiStatusException e) {
                    res = ExtHashSetOfQuasiStatuses.create(q.getSet());
                    }
                }
            }
            }

            /* multiset status */
            if(mul && !q.hasPermutation(fName) && !q.hasPermutation(gName) &&
               !q.hasFlatStatus(fName) && !q.hasFlatStatus(gName)) {
            final QuasiStatus tmp = q.deepcopy();
            tmp.assignMultisetStatus(fName);
            tmp.assignMultisetStatus(gName);

            try {
                res = res.union(ACQRPOS.minimalExt(s, t, tmp, eq, equal, lex, onlyLR, mul, flat, Cs)).minimalElements();
            }
            catch(final QuasiStatusException e) {
                res = ExtHashSetOfQuasiStatuses.create(q.getSet());
            }
            }

            /* flat status */
            if(flat && !q.hasPermutation(fName) && !q.hasPermutation(gName) &&
               !q.hasFlatStatus(fName) && !q.hasFlatStatus(gName) && f.getArity() == 2 && g.getArity()==2) {
            final QuasiStatus tmp = q.deepcopy();
            tmp.assignFlatStatus(fName);
            tmp.assignFlatStatus(gName);

            try {
                res = res.union(ACQRPOS.minimalExt(s, t, tmp, eq, equal, lex, onlyLR, mul, flat, Cs)).minimalElements();
            }
            catch(final QuasiStatusException e) {
                res = ExtHashSetOfQuasiStatuses.create(q.getSet());
            }
            }

            return res;
        }
        }
        if(!fName.equals(gName) && !q.areEquivalent(fName, gName)
           && (eq==null || eq.contains(Doubleton.create(fName, gName)))
           && !(((q.hasFlatStatus(fName) || q.hasFlatStatus(gName)))
            && (f.getArity()!=2 || g.getArity()!=2))) {

        final QuasiStatus tmp = q.deepcopy();
            try {
                tmp.setEquivalent(fName, gName);
            res = ACQRPOS.minimalExt(s, t, tmp, eq, equal, lex, onlyLR, mul, flat, Cs);
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
    if(FlattenedQuasiMultiterm.create(origS, this.statusMap, this.precedence).equals(FlattenedQuasiMultiterm.create(origT, this.statusMap, this.precedence))) {
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
            return this.precedence.isMinimal(tSymb.getName());
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
        final String fName = f.getName();
        final String gName = g.getName();
        if((fName.equals(gName) || this.precedence.areEquivalent(fName, gName))
           && f.getArity()==1) {
        return this.isGENGR(s.getArgument(0), t.getArgument(0));
        }
            if(fName.equals(gName)) {
        if(this.statusMap.hasPermutation(fName) || !this.statusMap.hasEntry(fName)) {
            final Iterator i1 = s.getArguments().iterator();
            final Iterator i2 = t.getArguments().iterator();
            boolean result = true;
            while(i1.hasNext() && result) {
            result = this.isGENGR((TRSTerm)i1.next(), (TRSTerm)i2.next());
            }
            return result;
        }
            else if(this.statusMap.hasFlatStatus(fName)) {
            /* AC status */
                final DoubleHash<TRSTerm,TRSTerm,Boolean> dh= DoubleHash.create();
                TRSTerm newLeft;
                TRSTerm newRight;

                    final ArrayList<TRSTerm> sArgs = FlattenedQuasiMultiterm.create(s, this.statusMap, this.precedence).getMultiArgumentsAsTermVector();
                    final ArrayList<TRSTerm> tArgs = FlattenedQuasiMultiterm.create(t, this.statusMap, this.precedence).getMultiArgumentsAsTermVector();

            if(sArgs.size()!=tArgs.size()) {
                return false;
            }

                final Iterator i = sArgs.iterator();
                    Iterator j;

                while(i.hasNext()) {
                newLeft = (TRSTerm)i.next();
                    j = tArgs.iterator();
                while(j.hasNext()) {
                    newRight = (TRSTerm)j.next();
                    dh.put(newLeft, newRight, Boolean.valueOf(this.isGENGR(newLeft, newRight)));
                }
                }

            final int n = sArgs.size();

                boolean result = false;
                for (final Permutation perm : PermutationGenerator.create(n)) {
                int index = 0;
                result = true;
                while(index<n && result) {
                    result = dh.get(sArgs.get(index), tArgs.get(perm.get(index)));
                index++;
                }
                        if (result) {
                            break;
                        }
                }
                return result;
            }
        else {
            /* multiset */
            Iterator<? extends TRSTerm> i1;
            Iterator<? extends TRSTerm> i2;

            final DoubleHash<TRSTerm,TRSTerm,Boolean> dh = DoubleHash.create();
            i1 = s.getArguments().iterator();
            while(i1.hasNext()) {
            final TRSTerm s_i = i1.next();
            i2 = t.getArguments().iterator();
            while(i2.hasNext()) {
                final TRSTerm t_j = i2.next();
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
                    result = dh.get(i1.next(), i2.next());
                }
                if (result) {
                    break;
                }
            }
            return result;
        }
        }
        else if(this.precedence.areEquivalent(fName, gName)) {
        if(!this.statusMap.hasEntry(fName) || !this.statusMap.hasEntry(gName)) {
            return false;
        }
        if(this.statusMap.hasPermutation(fName) && this.statusMap.hasPermutation(gName)) {
            final TRSTerm permS = LPOS.permuteTerm(s, this.statusMap.getPermutation(fName));
            final TRSTerm permT = LPOS.permuteTerm(t, this.statusMap.getPermutation(gName));
            final Iterator i1 = ((TRSFunctionApplication)permS).getArguments().iterator();
            final Iterator i2 = ((TRSFunctionApplication)permT).getArguments().iterator();
            boolean result = true;
            while(i1.hasNext() && result) {
            result = this.isGENGR((TRSTerm)i1.next(), (TRSTerm)i2.next());
            }

            return result;
        }
        else if(this.statusMap.hasMultisetStatus(fName) && this.statusMap.hasMultisetStatus(gName)) {
            Iterator<? extends TRSTerm> i1;
            Iterator<? extends TRSTerm> i2;

            final DoubleHash<TRSTerm,TRSTerm,Boolean> dh = DoubleHash.create();
            i1 = s.getArguments().iterator();
            while(i1.hasNext()) {
            final TRSTerm s_i = i1.next();
            i2 = t.getArguments().iterator();
            while(i2.hasNext()) {
                final TRSTerm t_j = i2.next();
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
                    result = dh.get(i1.next(), i2.next()).booleanValue();
                }
                if (result) {
                    break;
                }
            }
            return result;
        }
            else if(this.statusMap.hasFlatStatus(fName) && this.statusMap.hasFlatStatus(gName)) {
            /* AC status */
                final DoubleHash<TRSTerm,TRSTerm,Boolean> dh = DoubleHash.create();
                TRSTerm newLeft;
                TRSTerm newRight;

                    final ArrayList<TRSTerm> sArgs = FlattenedQuasiMultiterm.create(s, this.statusMap, this.precedence).getMultiArgumentsAsTermVector();
                    final ArrayList<TRSTerm> tArgs = FlattenedQuasiMultiterm.create(t, this.statusMap, this.precedence).getMultiArgumentsAsTermVector();

            if(sArgs.size()!=tArgs.size()) {
                return false;
            }

                final Iterator i = sArgs.iterator();
                    Iterator j;

                while(i.hasNext()) {
                newLeft = (TRSTerm)i.next();
                    j = tArgs.iterator();
                while(j.hasNext()) {
                    newRight = (TRSTerm)j.next();
                    dh.put(newLeft, newRight, Boolean.valueOf(this.isGENGR(newLeft, newRight)));
                }
                }

            final int n = sArgs.size();

                boolean result = false;
                    for (final Permutation perm : PermutationGenerator.create(n)) {
                int index = 0;
                result = true;
                while(index<n && result) {
                    result = dh.get(sArgs.get(index), tArgs.get(perm.get(index)));
                index++;
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

    /*
     *
     *
     *
     *
     *
     *
     *
     *
     *
     *
     *
     *
     *
     *
     *
     *
     *
     *
     *
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
    return FlattenedQuasiMultiterm.create(s, this.statusMap, this.precedence).equals(
           FlattenedQuasiMultiterm.create(t, this.statusMap, this.precedence));
    }

    /* We build a hashtble with the results of comparing the relevant subterms
     * of s and t.
     */
    private OrderRelation calculate(final TRSTerm origS, final TRSTerm origT) {
    boolean result=false;
    OrderRelation res;

    res = this.ho.get(origS, origT);
    if (res!= null) {
        /* we already know it */
        return res;
    }
    else {
        if(this.emb.inRelation(origS, origT)) {
                this.ho.put(origS, origT, OrderRelation.GR);
        this.ho.put(origT, origS, OrderRelation.NGE);
        return OrderRelation.GR;
        }

        /* we don't know about s and t yet */
        if(FlattenedQuasiMultiterm.create(origS, this.statusMap, this.precedence).equals(
           FlattenedQuasiMultiterm.create(origT, this.statusMap, this.precedence))) {
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
            final String symbLeftName = symbLeft.getName();
            final String symbRightName = symbRight.getName();

            TRSTerm s_i;
            TRSTerm t_i;

            final boolean eq = symbLeftName.equals(symbRightName) || this.precedence.areEquivalent(symbLeftName, symbRightName);

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
            else if(eq && this.statusMap.hasPermutation(symbLeftName)
                       && this.statusMap.hasPermutation(symbRightName)) {

            /* apply permutation */
            final Permutation pS = this.statusMap.getPermutation(symbLeftName);
            final Permutation pT = this.statusMap.getPermutation(symbRightName);
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
            else if(eq && this.statusMap.hasMultisetStatus(symbLeftName)
                       && this.statusMap.hasMultisetStatus(symbRightName)) {

            final MultiSet<TRSTerm> S = new HashMultiSet<TRSTerm>(s.getArguments());
            final MultiSet<TRSTerm> T = new HashMultiSet<TRSTerm>(t.getArguments());
            final MultisetExtension mul = MultisetExtension.create(this);
            result = mul.relate(S, T)==OrderRelation.GR;
            }
            else if(eq && this.statusMap.hasFlatStatus(symbLeftName)
                       && this.statusMap.hasFlatStatus(symbRightName)) {
            /* s' >= t for some s' from EmbNoBig(s)? */
            final FlattenedQuasiMultiterm sf = FlattenedQuasiMultiterm.create(s, this.statusMap, this.precedence);
            final FlattenedQuasiMultiterm tf = FlattenedQuasiMultiterm.create(t, this.statusMap, this.precedence);
            Set<FlattenedQuasiMultiterm> enb = sf.embNoBig(this.precedence);
            i = enb.iterator();
            while(i.hasNext() && result==false) {
                s_i = ((FlattenedQuasiMultiterm)i.next()).toTerm();
                res = this.calculate(s_i, t);
                if(res==OrderRelation.EQ || res==OrderRelation.GR || res==OrderRelation.GENGR) {
                result = true;
                }
            }
            if(!result) {
                /* Oh yeah! */
                /* s > t' for all t' from EmbNoBig(t)? */
                enb = tf.embNoBig(this.precedence);
                i = enb.iterator();
                result = true;
                while(i.hasNext() && result) {
                t_i = ((FlattenedQuasiMultiterm)i.next()).toTerm();
                res = this.calculate(s, t_i);
                    if(res!=OrderRelation.GR) {
                    result = false;
                }
                }
                if(result) {
                /* NoSmallHead(s) >>=_{pf} NoSmallHead(t)? */
                final MultiSet<TRSTerm> snsh = new HashMultiSet<TRSTerm>(FlattenedQuasiMultiterm.toTerm(sf.noSmallHead(this.precedence)));
                final MultiSet<TRSTerm> tnsh = new HashMultiSet<TRSTerm>(FlattenedQuasiMultiterm.toTerm(tf.noSmallHead(this.precedence)));
                    final MultisetExtension mul = MultisetExtension.create(new ACQRPOSf(this, symbLeftName));
                    res = mul.relate(snsh, tnsh);
                result = (res==OrderRelation.EQ || res==OrderRelation.GR);
                }
                if(result) {
                /* either BigHead(s) >> BigHead(t)? */
                final MultiSet<TRSTerm> sbh = new HashMultiSet<TRSTerm>(FlattenedQuasiMultiterm.toTerm(sf.bigHead(this.precedence)));
                final MultiSet<TRSTerm> tbh = new HashMultiSet<TRSTerm>(FlattenedQuasiMultiterm.toTerm(tf.bigHead(this.precedence)));
                    MultisetExtension mul = MultisetExtension.create(this);
                    result = mul.relate(sbh, tbh)==OrderRelation.GR;

                    if(!result) {
                    final SymbolicPolynomial sp = SymbolicPolynomial.createSymbolicPolynomial(sf);
                    final SymbolicPolynomial tp = SymbolicPolynomial.createSymbolicPolynomial(tf);
                    final OrderRelation cmp = sp.compareToPositive(tp);
                    if(cmp==OrderRelation.GR) {
                        /* or #(s) > #(t) */
                        result = true;
                    }
                    else if(cmp==OrderRelation.GE) {
                        /* or #(s) > #(t) and {s_1,...,s_n} >> {t_1,...,t_m} */
                            final MultiSet<TRSTerm> S = new HashMultiSet<TRSTerm>(sf.getMultiArgumentsAsTermVector());
                            final MultiSet<TRSTerm> T = new HashMultiSet<TRSTerm>(tf.getMultiArgumentsAsTermVector());
                            mul = MultisetExtension.create(this);
                            result = mul.relate(S, T)==OrderRelation.GR;
                    }
                }
                }
            }

            if(!result) {
                /* (2a) */
                final Iterator e = sf.getMultiArguments().keySet().iterator();
                while(e.hasNext() && !result) {
                final TRSTerm sub = ((FlattenedQuasiMultiterm)e.next()).toTerm();
                res = this.calculate(sub, t);
                if(res==OrderRelation.GR || res==OrderRelation.EQ || res==OrderRelation.GENGR) {
                    result = true;
                }
                }
            }
            }
            else if(this.precedence.isGreater(symbLeftName, symbRightName)) {
            /* f | g */
            /* (2c), no need for (2a) in this case */
                if(!this.statusMap.hasFlatStatus(symbRightName)) {
                    j = t.getArguments().iterator();
            }
                else {
                j = FlattenedQuasiMultiterm.create(t, this.statusMap, this.precedence).getMultiArguments().keySet().iterator();
            }

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
                if(this.statusMap.hasFlatStatus(symbLeftName)) {
                i = FlattenedQuasiMultiterm.create(s, this.statusMap, this.precedence).getMultiArguments().keySet().iterator();
            }
                else {
                i = s.getArguments().iterator();
            }

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
        return "AC-recursive path order with status "+eu.cite(Citation.ACRPOS)+"."
        +eu.linebreak()+QuasiStatus.create(this.precedence, this.statusMap).export(eu);
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
