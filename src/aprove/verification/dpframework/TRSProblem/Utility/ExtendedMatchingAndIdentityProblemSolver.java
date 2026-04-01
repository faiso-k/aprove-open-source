package aprove.verification.dpframework.TRSProblem.Utility;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * this class provides methods for solving EXTENDED and NON-EXTENDED MATCHING- and IDENTITY-PROBLEMS;
 * further methods for getting INCREASING VARIABLES of a Substitution "subst" and/or
 *      a CYCLEFREE Substitution subst^n are provided;
 *
 * to optimize computations, the solvability of upcoming
 *      Non-Extended Two-Term-Matching-Problems and Identity-Problems
 *          is STORED throughout the computation in the local Variable
 *              "knownMatchingAndIdentityProblems" which can also be accessed from outside
 *                  by a corresponding get()-method;
 * for each "main-substitution" "subst" occuring in context of Matching-/Identity-Problems one
 *      single instance of this class must be generated;
 *
 * NOTE:
 * if you are ONLY interested in Increasing Variables, use the method "getIncreasingVariables()";
 * if you are interested in a Cyclefree Substitution, DONT'T use the method "getIncreasingVariables()" before
 *      because then you compute Increasing Variables twice as the computations of these both overlay;
 * use the method "getIncreasingVariablesAndCycleFreeSubstitution" instead;
 *
 * the methods of this class for solving Non-Extended Matching- and Identity-Problems
 *      and for getting Increasing Variables and a Cyclefree Substitution
 *          have been copied and adjusted from the NonTerminationProcessor
 *
 * @author Sebastian Weise
 */

public class ExtendedMatchingAndIdentityProblemSolver {

    // the "main substitution" of the Matching-/Identity-Problem
    private final TRSSubstitution subst;

    private Set<TRSVariable> increasing;
    private TRSSubstitution cycleFree;

    private final KnownMatchingAndIdentityProblems knownMatchingAndIdentityProblems;

    public ExtendedMatchingAndIdentityProblemSolver(final TRSSubstitution subst) {
        this.subst = subst;
        this.knownMatchingAndIdentityProblems = new KnownMatchingAndIdentityProblems();
    }

    public TRSSubstitution getSubstitution() {
        return this.subst;
    }

    private class KnownMatchingAndIdentityProblems {

        // note that we work with the CLASS "Boolean" and NOT with the primitive class "boolean"
        // so we can handle the value "null" properly !

        private final Map<Pair<TRSTerm, TRSTerm>, Boolean> knownMatchingProblems;

        // here the Term-Pairs are ORDERED: pair.x.compareTo(pair.y) >= 0
        //      because non-extended Identity Problems are symmetric !
        private final Map<Pair<TRSTerm, TRSTerm>, Boolean> knownIdentityProblems;

        public KnownMatchingAndIdentityProblems() {
            this.knownMatchingProblems = new HashMap<Pair<TRSTerm, TRSTerm>, Boolean>();
            this.knownIdentityProblems = new HashMap<Pair<TRSTerm, TRSTerm>, Boolean>();
        }

        public Map<Pair<TRSTerm, TRSTerm>, Boolean> getKnownMatchingProblems() {
            return this.knownMatchingProblems;
        }

        public Map<Pair<TRSTerm, TRSTerm>, Boolean> getKnownIdentityProblems() {
            return this.knownIdentityProblems;
        }

        public void addToKnownMatchingProblems(final Pair<TRSTerm, TRSTerm> termPair,
                final Boolean solvable) {
            this.knownMatchingProblems.put(termPair, solvable);
        }

        // (only) if a GENERAL Matching Problem is solvable,
        //      we know that each contained single Matching Problem is also solvable!
        public void addToKnownMatchingProblems(
                final Set<Pair<TRSTerm, TRSTerm>> termPairs) {
            for (final Pair<TRSTerm, TRSTerm> actTermPair : termPairs) {
                this.knownMatchingProblems.put(actTermPair, Boolean.valueOf(true));
            }
        }

        public Boolean isSolvableAsMatchingProblem(
                final Pair<TRSTerm, TRSTerm> termPair) {
            return this.knownMatchingProblems.get(termPair);
        }

        public void addToKnownIdentityProblems(final Pair<TRSTerm, TRSTerm> termPair,
                final Boolean solvable) {
            this.knownIdentityProblems.put(this.orderTermPair(termPair),
                    solvable);
        }

        public Boolean isSolvableAsIdentityProblem(
                final Pair<TRSTerm, TRSTerm> termPair) {
            return this.knownIdentityProblems.get(this.orderTermPair(termPair));
        }

        private Pair<TRSTerm, TRSTerm> orderTermPair(final Pair<TRSTerm, TRSTerm> st) {
            final TRSTerm s = st.x;
            final TRSTerm t = st.y;

            if (s.compareTo(t) >= 0) {
                return st;
            } else {
                return new Pair<TRSTerm, TRSTerm>(t, s);
            }
        }
    }

    public Map<Pair<TRSTerm, TRSTerm>, Boolean> getKnownMatchingProblems() {
        return this.knownMatchingAndIdentityProblems.getKnownMatchingProblems();
    }

    public Map<Pair<TRSTerm, TRSTerm>, Boolean> getKnownIdentityProblems() {
        return this.knownMatchingAndIdentityProblems.getKnownIdentityProblems();
    }

    /**
     * this method returns the Variables that are INCREASING with respect to the Substitution "subst";
     * this method has been taken and adjusted from the NonTerminationProcessor
     */
    public Set<TRSVariable> getIncreasingVariables() {
        if (this.increasing == null) {
            // first compute increasing Variables
            this.increasing = new HashSet<TRSVariable>();
            final Map<TRSVariable, TRSVariable> nonIncreasing = new LinkedHashMap<TRSVariable, TRSVariable>();
            final Map<TRSVariable, ? extends TRSTerm> mu = this.subst.toMap();
            for (final Map.Entry<TRSVariable, ? extends TRSTerm> xt : mu.entrySet()) {
                if (xt.getValue().isVariable()) {
                    nonIncreasing.put(xt.getKey(), (TRSVariable) xt.getValue());
                } else {
                    this.increasing.add(xt.getKey());
                }
            }
            boolean change = true;
            while (change) {
                change = false;
                final Iterator<Map.Entry<TRSVariable, TRSVariable>> i = nonIncreasing
                        .entrySet().iterator();
                while (i.hasNext()) {
                    final Map.Entry<TRSVariable, TRSVariable> xy = i.next();
                    if (this.increasing.contains(xy.getValue())) {
                        this.increasing.add(xy.getKey());
                        i.remove();
                        change = true;
                    }
                }
            }
        }

        return this.increasing;
    }

    /**
     * this method returns both the
     *      Variables that are INCREASING with respect to the Substitution "subst" and
     *      a CYCLE-FREE Substitution subst^n
     *          (because the computations of these both overlay);
     * this method has been taken and adjusted from the NonTerminationProcessor
     */
    public Pair<Set<TRSVariable>, TRSSubstitution> getIncreasingVariablesAndCycleFreeSubstitution() {
        if (this.increasing == null || this.cycleFree == null) {

            // first compute increasing Variables

            this.increasing = new HashSet<TRSVariable>();
            final Map<TRSVariable, TRSVariable> nonIncreasing = new LinkedHashMap<TRSVariable, TRSVariable>();
            final Map<TRSVariable, ? extends TRSTerm> mu = this.subst.toMap();
            for (final Map.Entry<TRSVariable, ? extends TRSTerm> xt : mu.entrySet()) {
                if (xt.getValue().isVariable()) {
                    nonIncreasing.put(xt.getKey(), (TRSVariable) xt.getValue());
                } else {
                    this.increasing.add(xt.getKey());
                }
            }
            boolean change = true;
            while (change) {
                change = false;
                final Iterator<Map.Entry<TRSVariable, TRSVariable>> i = nonIncreasing
                        .entrySet().iterator();
                while (i.hasNext()) {
                    final Map.Entry<TRSVariable, TRSVariable> xy = i.next();
                    if (this.increasing.contains(xy.getValue())) {
                        this.increasing.add(xy.getKey());
                        i.remove();
                        change = true;
                    }
                }
            }

            // then find a cycle-free Substitution subst^n

            int j = 2;
            BigInteger n = BigInteger.ONE;
            this.cycleFree = this.subst;

            while (!nonIncreasing.isEmpty()) {
                final Iterator<Map.Entry<TRSVariable, TRSVariable>> i = nonIncreasing
                        .entrySet().iterator();
                while (i.hasNext()) {
                    final Map.Entry<TRSVariable, TRSVariable> xv = i.next();
                    final TRSVariable w = (TRSVariable) xv.getValue()
                            .applySubstitution(this.subst);
                    if (w.equals(xv.getKey())) {
                        i.remove();
                        final BigInteger m = n.multiply(BigInteger.valueOf(j))
                                .divide(n.gcd(BigInteger.valueOf(j)));
                        /*
                         * m =
                         * lcm(n,
                         * j)
                         */
                        if (!n.equals(m)) {
                            int fact = m.divide(n).intValue(); // new factor
                            final TRSSubstitution cycleFreeHelp = this.cycleFree;
                            while (fact != 1) {
                                this.cycleFree = this.cycleFree
                                        .compose(cycleFreeHelp);
                                fact--;
                            }
                            n = m;
                        }
                    } else if (mu.containsKey(w)) {
                        xv.setValue(w);
                    } else {
                        i.remove();
                    }
                }
                j++;
            }
        }

        return new Pair<Set<TRSVariable>, TRSSubstitution>(this.increasing,
                this.cycleFree);
    }

    /**
     * this method decides whether a given (general) MATCHING PROBLEM is solvable
     */
    public boolean solveMatchingProblem(final Set<Pair<TRSTerm, TRSTerm>> M) {

        // if this Matching Problem contains only one Pair of Terms, did we already solve it ??

        if (M.size() == 1) {
            for (final Pair<TRSTerm, TRSTerm> dummyTermPair : M) {
                final Boolean result = this.knownMatchingAndIdentityProblems
                        .isSolvableAsMatchingProblem(dummyTermPair);

                if (result != null) {
                    return result.booleanValue();
                }
            }
        }

        // the case above didn't apply, so let's continue

        if (this.increasing == null || this.cycleFree == null) {
            this.getIncreasingVariablesAndCycleFreeSubstitution();
        }

        final Comparator<Pair<TRSTerm, TRSTerm>> matchComparator = new Comparator<Pair<TRSTerm, TRSTerm>>() {
            // second argument first (and variables last)
            // => pairs (t,f(..)) will be in front
            @Override
            public int compare(final Pair<TRSTerm, TRSTerm> one,
                    final Pair<TRSTerm, TRSTerm> two) {
                final int cy = one.y.compareTo(two.y);
                if (cy == 0) {
                    return one.x.compareTo(two.x);
                } else {
                    return -cy;
                }
            }
        };

        Queue<Pair<TRSTerm, TRSTerm>> matchingProblem = new PriorityQueue<Pair<TRSTerm, TRSTerm>>(
                5, matchComparator);
        for (final Pair<TRSTerm, TRSTerm> termPair : M) {
            matchingProblem.offer(termPair);
        }

        final Collection<Collection<Set<TRSTerm>>> identProblems = new HashSet<Collection<Set<TRSTerm>>>();

        while (!matchingProblem.isEmpty()) {
            Pair<TRSTerm, TRSTerm> sq = matchingProblem.peek();
            final TRSTerm q = sq.y;
            if (q.isVariable()) {
                // we are done, so let us build identity problems
                final Map<TRSVariable, Set<TRSTerm>> ident = new HashMap<TRSVariable, Set<TRSTerm>>();
                for (final Pair<TRSTerm, TRSTerm> tx : matchingProblem) {
                    final TRSVariable x = (TRSVariable) tx.y; // this cast
                    // must
                    // succeed
                    // since if
                    // there is
                    // some pair
                    // with non-variable in second component then it
                    // should be returned by peek() instead of sq!
                    final TRSTerm t = tx.x;
                    Set<TRSTerm> tsForX = ident.get(x);
                    if (tsForX == null) {
                        tsForX = new HashSet<TRSTerm>();
                        ident.put(x, tsForX);
                    }
                    tsForX.add(t);
                }
                final Collection<Set<TRSTerm>> tsThatMustBecomeIdentical = new HashSet<Set<TRSTerm>>();
                for (final Set<TRSTerm> tsForX : ident.values()) {
                    if (tsForX.size() > 1) {
                        tsThatMustBecomeIdentical.add(tsForX);
                    }
                }
                if (tsThatMustBecomeIdentical.isEmpty()) {
                    this.knownMatchingAndIdentityProblems
                            .addToKnownMatchingProblems(M);

                    return true; // matching problem solvable
                }
                identProblems.add(tsThatMustBecomeIdentical);
                break;
            } else {
                // apply some matching rule
                final TRSTerm s = sq.x;
                if (s.isVariable()) {
                    if (this.increasing.contains(s)) {
                        // apply rule (i) (apply mu on all lhss)
                        final Queue<Pair<TRSTerm, TRSTerm>> newMatchProblem = new PriorityQueue<Pair<TRSTerm, TRSTerm>>(
                                matchingProblem.size(), matchComparator);
                        matchingProblem.poll();
                        do {
                            sq.x = sq.x.applySubstitution(this.subst);
                            newMatchProblem.offer(sq);
                            sq = matchingProblem.poll();
                        } while (sq != null);
                        matchingProblem = newMatchProblem;
                    } else {
                        // apply rule (ii)

                        if (M.size() == 1) {
                            for (final Pair<TRSTerm, TRSTerm> dummyTermPair : M) {
                                this.knownMatchingAndIdentityProblems
                                        .addToKnownMatchingProblems(
                                                dummyTermPair, Boolean.valueOf(
                                                        false));
                            }
                        }

                        return false;
                    }
                } else {
                    final TRSFunctionApplication fs = (TRSFunctionApplication) s;
                    final TRSFunctionApplication gq = (TRSFunctionApplication) q;
                    if (fs.getRootSymbol().equals(gq.getRootSymbol())) {
                        // apply rule (iv) (decompose)
                        matchingProblem.poll();
                        final List<? extends TRSTerm> ss = fs.getArguments();
                        final List<? extends TRSTerm> qs = gq.getArguments();
                        int i = 0;
                        for (final TRSTerm si : ss) {
                            final TRSTerm qi = qs.get(i);
                            matchingProblem.offer(new Pair<TRSTerm, TRSTerm>(si, qi));
                            i++;
                        }
                    } else {
                        // apply rule (iii)

                        if (M.size() == 1) {
                            for (final Pair<TRSTerm, TRSTerm> dummyTermPair : M) {
                                this.knownMatchingAndIdentityProblems
                                        .addToKnownMatchingProblems(
                                                dummyTermPair, Boolean.valueOf(
                                                        false));
                            }
                        }

                        return false;
                    }
                }
            }
        }

        /*
         * finally solve identity problems
         * (whenever one identProblem in identProblems is solved then a matching problem is solved,
         *  to solve one identProblem for each set of terms tsForX one has to make all terms t mu^n equal,
         *  and by assumption all these sets tsForX have at least two terms)
         */

        for (final Collection<Set<TRSTerm>> identProblem : identProblems) {
            // first flatten to binary
            final Set<Pair<TRSTerm, TRSTerm>> idProblems = new LinkedHashSet<Pair<TRSTerm, TRSTerm>>();
            for (final Set<TRSTerm> tsForX : identProblem) {
                for (final TRSTerm t1 : tsForX) {
                    for (final TRSTerm t2 : tsForX) {
                        if (t1.compareTo(t2) > 0) { // in this way we won't have duplicate pairs
                            idProblems.add(new Pair<TRSTerm, TRSTerm>(t1, t2));
                        }
                    }
                }
            }

            // check if all identityProblems in idProblems can be solved
            for (final Pair<TRSTerm, TRSTerm> idProblem : idProblems) {
                if (!this.solveIdentityProblem(idProblem.x, idProblem.y)) {
                    // this identProblem not solvable

                    if (M.size() == 1) {
                        for (final Pair<TRSTerm, TRSTerm> dummyTermPair : M) {
                            this.knownMatchingAndIdentityProblems
                                    .addToKnownMatchingProblems(dummyTermPair,
                                            Boolean.valueOf(false));
                        }
                    }

                    return false;
                }
            }
        }

        this.knownMatchingAndIdentityProblems.addToKnownMatchingProblems(M);

        return true;
    }

    /**
     * this method decides whether a given IDENTITY PROBLEM is solvable
     */
    public boolean solveIdentityProblem(TRSTerm s, TRSTerm t) {

        // did we already solve this Identity Problem ??

        final Boolean result = this.knownMatchingAndIdentityProblems
                .isSolvableAsIdentityProblem(new Pair<TRSTerm, TRSTerm>(s, t));

        if (result != null) {
            return result.booleanValue();
        }

        // the case above didn't apply, so let's continue

        if (this.increasing == null || this.cycleFree == null) {
            this.getIncreasingVariablesAndCycleFreeSubstitution();
        }

        final Set<TRSVariable> dom = this.cycleFree.getDomain();

        // internal data structure: List< position p, s|_p, t|_p > such that
        // everything above
        // the mentioned positions is identical
        Collection<Triple<Position, TRSTerm, TRSTerm>> workingList = new ArrayList<Triple<Position, TRSTerm, TRSTerm>>();
        final Position p = Position.create();
        if (!this.decompose(p, s, t, this.increasing, dom, workingList)) {
            this.knownMatchingAndIdentityProblems.addToKnownIdentityProblems(
                    new Pair<TRSTerm, TRSTerm>(s, t), Boolean.valueOf(false));

            return false;
        }

        // step (ii)
        final Map<TRSVariable, Collection<Triple<Position, TRSTerm, TRSTerm>>> S = new HashMap<TRSVariable, Collection<Triple<Position, TRSTerm, TRSTerm>>>();

        while (!workingList.isEmpty()) {
            final Collection<Triple<Position, TRSTerm, TRSTerm>> newWorkingList = new ArrayList<Triple<Position, TRSTerm, TRSTerm>>();
            for (final Triple<Position, TRSTerm, TRSTerm> pst : workingList) {
                s = pst.y;
                t = pst.z;
                if (this.increasing.contains(s)) {
                    if (!this.addToS(pst, S)) { // step (vii)
                        this.knownMatchingAndIdentityProblems
                                .addToKnownIdentityProblems(
                                        new Pair<TRSTerm, TRSTerm>(s, t),
                                        Boolean.valueOf(false));

                        return false; // step (viii)
                    }
                }
                if (this.increasing.contains(t)) {
                    if (!this.addToS(new Triple<Position, TRSTerm, TRSTerm>(pst.x, t,
                            s), S)) { // step (vii)
                        this.knownMatchingAndIdentityProblems
                                .addToKnownIdentityProblems(
                                        new Pair<TRSTerm, TRSTerm>(s, t),
                                        Boolean.valueOf(false));

                        return false; // step (viii)
                    }
                }
                // step (ix)
                s = s.applySubstitution(this.cycleFree);
                t = t.applySubstitution(this.cycleFree);
                if (!this.decompose(pst.x, s, t, this.increasing, dom,
                        newWorkingList)) {
                    this.knownMatchingAndIdentityProblems
                            .addToKnownIdentityProblems(new Pair<TRSTerm, TRSTerm>(s,
                                    t), Boolean.valueOf(false));

                    return false;
                }
            }

            workingList = newWorkingList; // step (x)
        }

        this.knownMatchingAndIdentityProblems.addToKnownIdentityProblems(
                new Pair<TRSTerm, TRSTerm>(s, t), Boolean.valueOf(true));

        return true;
    }

    /**
     * used to solve (non-extended) Identity Problems;
     * taken from the NonTerminationProcessor;
     *
     * adds the triple entry to S and returns false iff there is a conflict
     * due to step (vii)
     *
     * @param entry
     *            (the left term has to be an increasing variable, and the
     *            entry must be at a deepest position)
     * @param S
     */
    private boolean addToS(final Triple<Position, TRSTerm, TRSTerm> entry,
            final Map<TRSVariable, Collection<Triple<Position, TRSTerm, TRSTerm>>> S) {
        final TRSVariable x = (TRSVariable) entry.y;
        Collection<Triple<Position, TRSTerm, TRSTerm>> xEntries = S.get(x);
        if (xEntries == null) {
            xEntries = new ArrayList<Triple<Position, TRSTerm, TRSTerm>>();
            xEntries.add(entry);
            S.put(x, xEntries);
        } else {
            final TRSTerm u_2 = entry.z;
            final Position p_2 = entry.x;
            for (final Triple<Position, TRSTerm, TRSTerm> otherXEntry : xEntries) {
                if (Globals.useAssertions) {
                    assert (!otherXEntry.equals(entry)) : "I thought that the set S cannot contain duplicates by construction. "
                            + "Either this is a bug in the construction of S or my thought was wrong.";
                }
                final TRSTerm u_1 = otherXEntry.z;
                final Position p_1 = otherXEntry.x;
                if (u_1.equals(u_2)) {
                    if (p_1.isPrefixOf(p_2)) {
                        // note that by assertion p_1 cannot be the same as
                        // p_2 at this point
                        // hence the check is a proper prefix check.
                        // Moreover, since the newly created entry is at a
                        // lowest position,
                        // we do not have to try to exchange p_1 and p_2
                        return false; // step (viii-b)
                    }
                } else {
                    if (!u_1.unifies(u_2)) {
                        return false; // step (viii-a)
                    }
                }
            }

            // no conflict, so add the new entry
            xEntries.add(entry);
        }
        return true;
    }

    /**
     * used to solve (non-extended) Identity Problems;
     * taken from the NonTerminationProcessor;
     *
     * adds all (p',s|_p',t|_p') to todo such that p' is below p, p' is a
     * deepest shared position, s and t differ at position p' all triples
     * that are added may be solvable (if mu is defined accordingly)
     * (conflicts with (iv),(v),(vi) are detected)
     *
     * @param p
     * @param s
     * @param t
     * @param increasing
     * @param dom
     * @param todo
     * @return false, if a conflict occurred, true otherwise.
     */
    private boolean decompose(final Position p, final TRSTerm s, final TRSTerm t,
            final Set<TRSVariable> increasing, final Set<TRSVariable> dom,
            final Collection<Triple<Position, TRSTerm, TRSTerm>> todo) {
        if (s.isVariable()) {
            if (s.equals(t)) {
                return true; // step (iii)
            } else {
                if (t.isVariable()) {
                    if (!dom.contains(s) && !dom.contains(t)) {
                        return false; // step (vi)
                    } else {
                        todo.add(new Triple<Position, TRSTerm, TRSTerm>(p, s, t));
                        return true;
                    }
                } else {
                    if (increasing.contains(s)) {
                        todo.add(new Triple<Position, TRSTerm, TRSTerm>(p, s, t));
                        return true;
                    } else {
                        return false; // step (v)
                    }
                }
            }
        } else {
            if (t.isVariable()) {
                if (increasing.contains(t)) {
                    todo.add(new Triple<Position, TRSTerm, TRSTerm>(p, s, t));
                    return true;
                } else {
                    return false; // step (v) (one can easily replace
                    // "notin Dom(mu)" by "not in increasing"
                    // in step (v))
                }
            } else {
                final TRSFunctionApplication fs = (TRSFunctionApplication) s;
                final TRSFunctionApplication gt = (TRSFunctionApplication) t;
                if (fs.getRootSymbol().equals(gt.getRootSymbol())) {
                    int i = 0; // step (iii) (on top level + decomposition)
                    final List<? extends TRSTerm> ts = gt.getArguments();
                    for (final TRSTerm si : fs.getArguments()) {
                        final TRSTerm ti = ts.get(i);
                        final Position pi = p.append(i);
                        if (!this.decompose(pi, si, ti, increasing, dom, todo)) {
                            return false;
                        }
                        i++;
                    }
                    return true;
                } else {
                    return false; // step (vi)
                }
            }
        }
    }

    /**
     * this method decides whether a given EXTENDED MATCHING PROBLEM is solvable,
     * requires that D is a proper subcontext of C.
     */
    public boolean solveExtendedMatchingProblem(Context D, TRSTerm l, Context C,
            TRSTerm t, final Set<Pair<TRSTerm, TRSTerm>> M) {

        if (this.increasing == null || this.cycleFree == null) {
            this.getIncreasingVariablesAndCycleFreeSubstitution();
        }

        // first transform the extended Matching Problem to reach "Solved Form" or detect Solvability/Non-Solvability

        TRSTerm lJ, sJ;

        loop: do {
            if (!l.isVariable()) {
                if (!D.isEmptyContext()) {
                    NonEmptyContext neD = (NonEmptyContext) D;
                    final int DdirectSubcontextPosition = neD
.getPositionOfDirectSubcontext();
                    final TRSFunctionApplication lApp = (TRSFunctionApplication) l;

                    if (neD.getRootSymbol().equals(lApp.getRootSymbol())) {

                        /* Rule (i) */

                        for (int i = 0; i <= neD.getArity() - 1
                                && i != DdirectSubcontextPosition; i++) {
                            M.add(new Pair<TRSTerm, TRSTerm>(neD.getArgument(i), lApp
                                    .getArgument(i)));
                        }

                        D = neD.getDirectSubcontext();
                        l = lApp.getArgument(DdirectSubcontextPosition);

                        continue loop;
                    } else {

                        /* Rule (iii) */

                        return false;
                    }
                } else {
                    final Set<Pair<TRSTerm, TRSTerm>> Mnew = new HashSet<Pair<TRSTerm, TRSTerm>>(
                            M);

                    Mnew.add(new Pair<TRSTerm, TRSTerm>(t, l));

                    if (this.solveMatchingProblem(Mnew)) {

                        /* Rule (vii) */

                        return true;
                    } else {

                        /* Rule (viii) */

                        D = C;
                        C = C.applySubstitution(this.subst);
                        t = t.applySubstitution(this.subst);

                        continue loop;
                    }
                }
            } else {
                for (final Pair<TRSTerm, TRSTerm> termPairOne : M) {
                    lJ = termPairOne.y;

                    if (!lJ.isVariable()) {
                        sJ = termPairOne.x;

                        if (sJ instanceof TRSFunctionApplication) {
                            final TRSFunctionApplication lJapp = (TRSFunctionApplication) lJ;
                            final FunctionSymbol lJappF = lJapp.getRootSymbol();
                            final TRSFunctionApplication sJapp = (TRSFunctionApplication) sJ;
                            final FunctionSymbol sJappF = sJapp.getRootSymbol();

                            if (lJappF.equals(sJappF)) {

                                /* Rule (ii) */

                                M.remove(termPairOne);

                                for (int i = 0; i <= lJappF.getArity() - 1; i++) {
                                    M.add(new Pair<TRSTerm, TRSTerm>(sJapp
                                            .getArgument(i), lJapp
                                            .getArgument(i)));
                                }

                                continue loop;
                            } else {

                                /* Rule (iv) */

                                return false;
                            }
                        } else {
                            if (!this.increasing.contains(sJ)) {

                                /* Rule (v) */

                                return false;
                            } else {

                                /* Rule (vi) */

                                D = D.applySubstitution(this.subst);
                                C = C.applySubstitution(this.subst);
                                t = t.applySubstitution(this.subst);

                                for (final Pair<TRSTerm, TRSTerm> termPairTwo : M) {
                                    termPairTwo.x = termPairTwo.x
                                            .applySubstitution(this.subst);
                                }

                                continue loop;
                            }
                        }
                    }
                }
            }

            break loop;
        } while (true);

        // extended Matching Problem in "Solved Form" now

        final ArrayList<Pair<TRSTerm, TRSTerm>> Marray = new ArrayList<Pair<TRSTerm, TRSTerm>>(
                M);

        for (final Pair<TRSTerm, TRSTerm> termPair : Marray) {
            if (l.equals(termPair.y)) { // "l" Variable now !
                // it suffices to consider the non-extended identity problem, see IsaFoR-formalization
                if  (!this.solveIdentityProblem(D.replace(t), termPair.x)) {
                    return false;
                }

                break;
            }
        }

        for (int i = 1; i <= Marray.size() - 1; i++) {
            for (int j = 0; j <= i - 1; j++) {
                if (Marray.get(i).y.equals(Marray.get(j).y)) {

                    if (!this.solveIdentityProblem(Marray.get(j).x, Marray
                            .get(i).x)) {
                        return false;
                    }

                    break;
                }
            }
        }

        return true;
    }

}
