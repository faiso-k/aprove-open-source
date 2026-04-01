/*
 * Created on 16.04.2005
 */
package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * The narrowing processor as in Thm. 5.19 (diss Rene)
 * (if positional is true, default)
 * (positional = false should only be used to see advantages of positional narrowing)
 *
 * Its application is as follows: We require that the usable rule
 * processor was used before and that the d-graph processor was used before!
 *
 * @author thiemann
 */
public class QDPNarrowingProcessor extends QDPTransformationProcessor {

    private final boolean beComplete;
    private final boolean positional;
    private final boolean nonRecHeuristic;

    @ParamsViaArgumentObject
    public QDPNarrowingProcessor(final Arguments arguments) {
        super(QDPTransformation.Narrowing, arguments);
        this.beComplete = arguments.beComplete;
        this.positional = arguments.positional;
        this.nonRecHeuristic = arguments.nonrecursiveHeuristic;
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        // demand graph-reduces, and a nonempty R
        // moreover Q = empty or (Q superset of R and usable rules proc was applied)
        return super.isQDPApplicable(qdp) && !qdp.getR().isEmpty() && (qdp.getQ().isEmpty() || (qdp.QsupersetOfLhsR() && qdp.getR().size() == qdp.getUsableRules().size()));
    }

    @Override
    protected AbortableIterator<Quadruple<TransformationHeuristic, YNMImplication, Set<Pair<Rule, Rule>>, Triple<Position, Set<Rule>, Rule>>> getTransformedRules(final Node<Rule> s_to_t,
        final Graph<Rule, ?> gr,
        final QDPProblem qdp,
        final Abortion aborter) throws AbortionException {

        // determine redexes // perhaps cache these results

        final QTRSProblem qtrs = qdp.getRwithQ();
        final QTermSet Q = qdp.getQ();
        final boolean innermost = qtrs.QsupersetOfLhsR();
        final Rule sToT = s_to_t.getObject().getWithRenumberedVariables(TRSTerm.SECOND_STANDARD_PREFIX);

        final TRSTerm t = sToT.getRight();

        // for termination we require a linear t
        if (!innermost && !t.isLinear()) {
            return QDPTransformationProcessor.EMPTY_ITERATOR;
        }

        aborter.checkAbortion();

        // and there are non-unification conditions if
        // there not already is a Q-redex in t
        final Set<Node<Rule>> successors = gr.getOut(s_to_t);
        final Set<Rule> succs = new LinkedHashSet<Rule>(successors.size());

        if (!this.positional || !Q.canBeRewritten(t)) {
            for (final Node<Rule> successor : gr.getOut(s_to_t)) {
                if (succs.add(successor.getObject())) {
                    //successor.getObject().getLhsInStandardRepresentation().unifies(t);
                    final TRSTerm u = successor.getObject().getLhsInStandardRepresentation();
                    final TRSSubstitution mu = u.getMGU(t);
                    if (mu != null) {
                        aborter.checkAbortion();
                        final TRSTerm uMu = u.applySubstitution(mu);
                        final TRSTerm s = sToT.getLeft();
                        final TRSTerm sMu = s.applySubstitution(mu);
                        if ((!Q.canBeRewritten(uMu)) && (!Q.canBeRewritten(sMu))) {
                            return QDPTransformationProcessor.EMPTY_ITERATOR;
                        }
                    }
                }
            }
        } else {
            for (final Node<Rule> successor : gr.getOut(s_to_t)) {
                succs.add(successor.getObject());
            }
        }


        // okay, it is allowed to narrow, so let us do it

        // first determine a position where we can narrow
        // i.e. we only have to do narrowing steps below this position

        final Collection<Position> positionsToNarrow;

        if (this.positional) {
            final TRSTerm cappedT = qdp.getQUsableRulesCalculator().getCappedDP(sToT).getRight();
            final NarrowingPosition ps = new NarrowingPosition(t, cappedT,Q);
            for (final Rule succ : succs) {
                ps.restrictToTermPositions(succ.getLhsInStandardRepresentation());
            }

            for (final Rule succ : succs) {
                aborter.checkAbortion();
                final boolean res = ps.restrictToNonUnifiers(succ.getLhsInStandardRepresentation());
                if (Globals.useAssertions) {
                    assert(!res);
                    // we have checked earlier that epsilon is a possible position where there is no unifier possible
                }
            }

            if (Globals.useAssertions) {
                for (final Position p : ps.getPositions()) {
                    TRSTerm tp = t.getSubterm(p);
                    final boolean redex = Q.canBeRewritten(tp);
                    if (!redex) {
                        assert(cappedT.getPositions().contains(p));
                        tp = tp.renumberVariables("a");
                        for (final Rule succ : succs) {
                            final TRSTerm succLeft = succ.getLeft().renumberVariables("b");
                            final TRSSubstitution mgu = succLeft.getSubterm(p).getMGU(tp);
                            if (mgu != null) {
                                final TRSTerm succLeftSigma = succLeft.applySubstitution(mgu);
                                assert(Q.canBeRewritten(succLeftSigma));
                            }
                        }
                    }
                }
            }

            positionsToNarrow = ps.getPositions();
        } else {
            // epsilon can always be chosen but may lead to more new rules
            // than a better position (epsilon is classical narrowing)
            positionsToNarrow = new ArrayList<Position>(1);
            positionsToNarrow.add(Position.create());
        }



        final Map<FunctionSymbol, ImmutableSet<Rule>> ruleMap = qtrs.getRuleMap();
        final Set<Rule> newRules = new LinkedHashSet<Rule>(5);
        final Set<Pair<Rule, Rule>> resRules = new LinkedHashSet<>(5);
        final Set<FunctionSymbol> narrowedFunctions = new LinkedHashSet<FunctionSymbol>(4);


        final Set<Rule> narrowedSubterms = new LinkedHashSet<Rule>(5);

        final TRSFunctionApplication s = sToT.getLeft();

        final Iterator<Position> positionsIter = positionsToNarrow.iterator();

        return new AbortableIterator<Quadruple<TransformationHeuristic, YNMImplication, Set<Pair<Rule, Rule>>, Triple<Position, Set<Rule>, Rule>>>() {

            private void computeNext(final Abortion aborter) throws AbortionException {

                while (positionsIter.hasNext()) {

                    final Position positionToNarrow = positionsIter.next();

                    // so we have to narrow the corresponding subterm
                    final TRSTerm tp = t.getSubterm(positionToNarrow);

                    // first initialize the corresponding sets
                    if (!newRules.isEmpty()) {
                        newRules.clear();
                        resRules.clear();
                    }
                    if (!narrowedFunctions.isEmpty()) {
                        narrowedFunctions.clear();
                    }

                    if (innermost) {
                        if (!narrowedSubterms.isEmpty()) {
                            narrowedSubterms.clear();
                        }
                    }

                    // then compute all narrowings
                    for (final Pair<Position, TRSTerm> posWithSub : tp.getPositionsWithSubTerms()) {

                        final TRSTerm subTerm = posWithSub.y;
                        if (!subTerm.isVariable()) {
                            aborter.checkAbortion();
                            final TRSFunctionApplication sub = (TRSFunctionApplication) subTerm;
                            final FunctionSymbol f = sub.getRootSymbol();
                            final Set<Rule> possibleRules = ruleMap.get(f);
                            if (possibleRules != null) {
                                for (final Rule rule : possibleRules) {
                                    final TRSFunctionApplication l = rule.getLhsInStandardRepresentation();
                                    final TRSSubstitution unifier = l.getMGU(subTerm);
                                    if (unifier != null) {
                                        // okay, we can narrow

                                        final TRSFunctionApplication sMu = s.applySubstitution(unifier);
                                        if (innermost) {
                                            final TRSFunctionApplication lMu = l.applySubstitution(unifier); // should be equal to t \mu|_p'
                                            if (!(Q.canBeRewritten(sMu) || Q.canBeRewrittenBelowRoot(lMu))) { // sMu and subterms of lMu should be Q-normal
                                                narrowedFunctions.add(f);
                                                final Rule generatedRule =
                                                    Rule.create(
                                                        sMu,
                                                        t.replaceAt(
                                                            positionToNarrow,
                                                            tp.replaceAt(posWithSub.x,
                                                                rule.getRhsInStandardRepresentation())).applySubstitution(
                                                            unifier));
                                                final Rule newRule = qdp.getPair(generatedRule);
                                                newRules.add(newRule);
                                                resRules.add(new Pair<>(generatedRule, newRule));
                                                narrowedSubterms.add(Rule.create(sMu, lMu));
                                            }
                                        } else {
                                            narrowedFunctions.add(f);
                                            final Rule generatedRule =
                                                Rule.create(
                                                    sMu,
                                                    t.replaceAt(
                                                        positionToNarrow,
                                                        tp.replaceAt(posWithSub.x,
                                                            rule.getRhsInStandardRepresentation())).applySubstitution(
                                                        unifier));
                                            final Rule newRule = qdp.getPair(generatedRule);
                                            newRules.add(newRule);
                                            resRules.add(new Pair<>(generatedRule, newRule));
                                        }

                                    }
                                }
                            }
                        }
                    }

                    YNMImplication complete;

                    if (!innermost || QDPNarrowingProcessor.this.checkCompleteness(qdp, Rule.create(s, tp), narrowedSubterms, aborter)) {
                        complete = YNMImplication.EQUIVALENT;
                    } else {
                        complete = YNMImplication.SOUND;
                    }

                    if (!QDPNarrowingProcessor.this.beComplete || complete == YNMImplication.EQUIVALENT) {
                        final TransformationHeuristic th = QDPNarrowingProcessor.this.nonRecHeuristic ? new TransformationHeuristic() {

                            @Override
                            public boolean safeTransformation() {
                                for (final FunctionSymbol f : narrowedFunctions) {
                                    if (qtrs.isRecursive(f)) {
                                        return false;
                                    }
                                }
                                return true;
                            }

                        } : null;

                        this.nextSolution =
                            new Quadruple<TransformationHeuristic, YNMImplication, Set<Pair<Rule, Rule>>, Triple<Position, Set<Rule>, Rule>>(
                                th, complete, resRules, new Triple<Position, Set<Rule>, Rule>(positionToNarrow, null,
                                    null));
                        this.nextValid = true;
                        return;
                    }

                }

                this.nextSolution = null;
                this.nextValid = true;

            }

            Quadruple<TransformationHeuristic, YNMImplication, Set<Pair<Rule, Rule>>, Triple<Position, Set<Rule>, Rule>> nextSolution =
                null;
            boolean nextValid = false;

            @Override
            public boolean hasNext(final Abortion aborter) throws AbortionException {
                if (!this.nextValid) {
                    this.computeNext(aborter);
                }
                return this.nextSolution != null;
            }

            @Override
            public Quadruple<TransformationHeuristic, YNMImplication, Set<Pair<Rule, Rule>>, Triple<Position, Set<Rule>, Rule>> next(final Abortion aborter)
                    throws AbortionException {
                if (!this.nextValid) {
                    this.computeNext(aborter);
                }
                this.nextValid = false;
                return this.nextSolution;
            }

        };


    }


    /**
     * only call if Q is non-empty
     * @param qdp
     * @param s_to_tp
     * @param instantiatedRules - the rule s\mu -> t\mu|_p' from the the narrowing (where the rewrite has not yet been performed)
     * @param aborter
     * @return
     * @throws AbortionException
     */
    private boolean checkCompleteness(final QDPProblem qdp, final Rule s_to_tp, final Set<Rule> instantiatedRules, final Abortion aborter) throws AbortionException {

        if (Globals.useAssertions) {
            assert(!qdp.getQ().isEmpty());
        }

        // note that l -> r as in rene's diss is always included in our estimation of usable rules!
        final QUsableRules usableRulesCalc = qdp.getQUsableRulesCalculator();

        if (!usableRulesCalc.getQRNormal(s_to_tp)) {
            // okay, s_to_tp might be to coarse, lets do finer checks;
            for (final Rule sMu_to_tMuPprime : instantiatedRules) {
                if (!usableRulesCalc.getQRNormal(sMu_to_tMuPprime)) {
                    // okay, no way to obtain completeness here
                    return false;
                }
            }

            // coarse check failed, but finer check was okay.

        }

        // and check for non-overlapping usable rules or that the Cap(tmu|p') = tmu|p' condition is satisfied
        if (!qdp.getRwithQ().getCriticalPairs().isNonOverlapping(aborter)) {
            // okay, we have at least some critical pair in used(P,R)
            // (note that U(P,R) = R by the application criteria) and that often this set is precomputed

            // if we have overlapping rules we do finer analysis

            for (final Rule sMu_to_tMuPprime : instantiatedRules) {
                // first check cap-condition
                final TRSFunctionApplication sMu = sMu_to_tMuPprime.getLeft();
                final TRSFunctionApplication tMuP = (TRSFunctionApplication) sMu_to_tMuPprime.getRight();
                boolean capOkay = true;
                final Iterator<? extends TRSTerm> argIt = tMuP.getArguments().iterator();
                while (capOkay && argIt.hasNext()) {
                    final Rule s_to_tMuPprimeI = Rule.create(sMu, argIt.next());
                    final GeneralizedRule capped = usableRulesCalc.getCappedDP(s_to_tMuPprimeI);
                    capOkay = capped.equals(s_to_tMuPprimeI);
                }
                if (capOkay) {
                    // cap-condition was successful, so we do not have to compute usable rules
                    continue;
                }

                // if the above check failrs then try criterion
                //  that there are only trivial critical pairs of the usable rules (implies confluence, but is
                //  weaker than statement in diss of rene)
                final Set<Rule> usable = usableRulesCalc.getUsableRules(sMu_to_tMuPprime);
                final AbortableIterator<ImmutableTriple<TRSTerm, TRSTerm, Boolean>> it = GeneralizedRule.getCriticalPairs(usable);
                while (it.hasNext(aborter)) {
                    final ImmutableTriple<TRSTerm, TRSTerm, Boolean> critPair = it.next(aborter);
                    if (!critPair.x.equals(critPair.y)) {
                        return false;
                    }
                }
            }


        }

        return true;

    }

    /**
     * this class stores and computes a set of independent deepest possible positions efficiently.
     * Allowed positions as in Narrowing Processor of Thm 5.19 (diss Rene)
     */
    private static class NarrowingPosition {

        private final static Map<Integer, NarrowingPosition> EMPTY_MAP = new HashMap<Integer, NarrowingPosition>(0);

        private final boolean containsRedex; // is there a Q-redex (non-strictly) below? (Then we don't throw away that position because of cap,..)
        private boolean checkCap; // does it make sense to check for cap/unif condition? (this is not the case if already have a Q-redex below,
                                    // and cap/unif criterion cannot choose a deeper position)

        private Map<Integer, NarrowingPosition> map; // the mapping from argument-positions to more positions.
        private final TRSTerm t; // the term at the current position
        private final QTermSet Q;

        /**
         * both t and cappedT must not contain vars from STANDARD_PREFIX
         * @param t
         * @param cappedT null, if we are below cappedT
         */
        /*
         * In the constructors, conditions on Q-redex and on cap will be checked.
         * Later the methods for checking positions in u and unif-conditions must be checked.
         */
        NarrowingPosition(final TRSTerm t, final TRSTerm cappedT, final QTermSet Q) {
            this.t = t;
            this.Q = Q;
            if (t.isVariable()) {
                this.containsRedex = false;
                if (cappedT == null) {
                    this.checkCap = false;
                    this.map = NarrowingPosition.EMPTY_MAP;
                } else {
                    this.checkCap = true;
                    this.map = NarrowingPosition.EMPTY_MAP;
                }
            } else {
                final TRSFunctionApplication ft = (TRSFunctionApplication) t;
                if (cappedT == null || cappedT.isVariable()) {
                    final List<? extends TRSTerm> targs = ft.getArguments();
                    final int n = targs.size();
                    this.map = new LinkedHashMap<Integer, NarrowingPosition>(n);
                    for (int i=0; i<n; i++) {
                        // below we can only obtain RedexFinal or Unusable States
                        final NarrowingPosition np = new NarrowingPosition(targs.get(i), null,Q);
                        if (np.containsRedex) {
                            this.map.put(i, np);
                        }
                    }
                    if (this.map.isEmpty()) { // if there is no redex below the root then
                        // perhaps we have a root redex
                        if (Q.canBeRewrittenAtRoot(ft)) {
                            // then since cap does not reach deeper we do not have to check for cap
                            this.containsRedex = true;
                            this.checkCap = false;
                        } else {
                            this.containsRedex = false;
                            // there is no redex but we might be at a position in cap
                            this.checkCap = cappedT != null;
                        }
                    } else {
                        this.containsRedex = true;
                        this.checkCap = false;
                    }
                } else {
                    // capped term is non-variable
                    final TRSFunctionApplication fcap = (TRSFunctionApplication) cappedT;
                    final List<? extends TRSTerm> capargs = fcap.getArguments();
                    final List<? extends TRSTerm> targs = ft.getArguments();
                    final int n = capargs.size();
                    this.map = new LinkedHashMap<Integer, NarrowingPosition>(n);
                    boolean redexBelow = false;
                    boolean checkCapBelow = false;
                    for (int i=0; i<n; i++) {
                        final NarrowingPosition np = new NarrowingPosition(targs.get(i), capargs.get(i),Q);
                        this.map.put(i, np);
                        redexBelow |= np.containsRedex;
                        checkCapBelow |= np.checkCap;
                    }
                    this.containsRedex = redexBelow || Q.canBeRewrittenAtRoot(ft);
                    if (checkCapBelow) {
                        this.checkCap = true;
                    } else {
                        // if we don't have to check below,
                        // then we should only consider this position,
                        // if we don't have a redex.
                        this.checkCap = !this.containsRedex;
                    }
                }
            }
        }

        /**
         * says that all positions below this narrowing positions which
         * are still present due to cap-condition should be removed
         * @param strictlyBelow only remove strictly below positions
         */
        private void removeCapBelow(final boolean strictlyBelow) {
            if (this.checkCap) {
                this.checkCap = strictlyBelow && !this.containsRedex;
                if (this.containsRedex) {
                    final Iterator<NarrowingPosition> i = this.map.values().iterator();
                    while (i.hasNext()) {
                        final NarrowingPosition np = i.next();
                        if (!np.containsRedex) {
                            i.remove();
                        } else {
                            np.removeCapBelow(false);
                        }
                    }
                } else {
                    this.map = NarrowingPosition.EMPTY_MAP;
                }
            }
        }

        /**
         * deletes all positions that are not present in the given term
         * (w.r.t. cap-positions)
         * @param term
         */
        void restrictToTermPositions(final TRSTerm term) {
            if (this.checkCap) {
                if (term.isVariable()) {
                    this.removeCapBelow(true);
                } else {
                    final TRSFunctionApplication ft = (TRSFunctionApplication) term;
                    boolean checkCapBelow = false;
                    for (final Map.Entry<Integer, NarrowingPosition> entry : this.map.entrySet()) {
                        final NarrowingPosition np = entry.getValue();
                        np.restrictToTermPositions(ft.getArgument(entry.getKey().intValue()));
                        checkCapBelow |= np.checkCap;
                    }
                    // if there is no need to check Cap below
                    // then there is no need to check this position if we have a redex
                    if (!checkCapBelow && this.containsRedex) {
                        this.checkCap = false;
                    }
                }
            }
        }

        /**
         * All cap-positions where a unification between given term and internal term is possible are deleted.
         * (+ some normal form checks on unifier)
         * @param term - a term with variables only from STANDARD_PREFIX
         * @return true iff the given term can be unified with the internal term such that the position is deleted
         */
        boolean restrictToNonUnifiers(final TRSTerm term) {
            if (this.checkCap) {

                // first try to delete in children;
                if (!term.isVariable()) {
                    final TRSFunctionApplication ft = (TRSFunctionApplication) term;
                    final Iterator<Map.Entry<Integer, NarrowingPosition>> i = this.map.entrySet().iterator();
                    boolean checkCapBelow = false;
                    while(i.hasNext()) {
                        final Map.Entry<Integer, NarrowingPosition> entry = i.next();
                        final NarrowingPosition np = entry.getValue();
                        final boolean argUnif = np.restrictToNonUnifiers(ft.getArgument(entry.getKey().intValue()));
                        if (argUnif) {
                            // okay, this position cannot be used, so delete it
                            i.remove();
                        } else {
                            checkCapBelow |= np.checkCap;
                        }
                    }
                    if (!checkCapBelow && this.containsRedex) {
                        this.checkCap = false;
                    }
                }
                if (this.map.isEmpty() && !this.containsRedex) {
                    // if all children have already been removed and we don't have a redex then perhaps
                    // we must remove this position, too
                    // let's check for unification at the root
                    final TRSSubstitution subs =  term.getMGU(this.t);
                    // only unifiable if t*subs and term*subs in Q-normalform;
                    return (subs != null) && (!this.Q.canBeRewritten(term.applySubstitution(subs))) && (!this.Q.canBeRewritten(term.applySubstitution(subs)));
                } else {
                    // if the map is non-empty or we have a redex then don't delete this position
                    return false;
                }
            } else {
                return false;
            }
        }

        /**
         * returns all positions possible for narrowing, i.e. p-narrowing is possible for these positions
         * @return
         */
        Collection<Position> getPositions() {
            final Position p = Position.create();
            final Collection<Position> ps = new ArrayList<Position>();
            this.addPositions(p, ps);
            return ps;
        }

        private void addPositions(final Position p, final Collection<Position> ps) {
            if (this.map.isEmpty()) {
                ps.add(p);
            } else {
                for (final Map.Entry<Integer, NarrowingPosition> entry : this.map.entrySet()) {
                    entry.getValue().addPositions(p.append(entry.getKey().intValue()), ps);
                }
            }
        }

        /**
         * gets one deepest position
         */
        Position getOnePosition() {
            Position p = Position.create();
            NarrowingPosition np = this;
            while (!np.map.isEmpty()) {
                final Map.Entry<Integer, NarrowingPosition> entry = np.map.entrySet().iterator().next();
                p = p.append(entry.getKey().intValue());
                np = entry.getValue();
            }
            return p;
        }

        @Override
        public String toString() {
            return this.getPositions().toString();
        }

    }

    public static class Arguments extends QDPTransformationProcessor.Arguments {
        public boolean beComplete = false;
        public boolean nonrecursiveHeuristic = true;
        public boolean positional = true;
    }

}
