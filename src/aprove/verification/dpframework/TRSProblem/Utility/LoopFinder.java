package aprove.verification.dpframework.TRSProblem.Utility;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * this class provides a (public) method
 *      "Set<Loop> getLoops(final Abortion aborter) throws AbortionException"
 *          which searchs for a QDP-Loop
 *              using (private) help-methods from the NonTerminationProcessor
 *          and returns a corresponding Set of TRS-Loops;
 *          this method can be executed SEVERAL times
 *              and always continues the search FROM THE LAST POINT OF STATE!
 *          the Loops are CHECKED for Soundness before they are returned;
 *          once the method has returned NULL,
 *              either NO MORE TRS-Loops will be found or
 *              an Error occured during a Loop-Check
 *                  (in this case a corresponding Log-Info will be given)!
 * the main task consists in re-building the CONTEXTS
 *      which go lost during the search for a QDP-Loop
 *
 * @author Sebastian Weise
 */

public class LoopFinder {

    /**
     * needed for the search for TRS-Loops
     */
    private NonTerminationProcedure nonTermProc;

    /**
     * needed to keep track of the search for a QDP-Loop
     */
    private static enum Status {
        pRulesCheck, closureCheckOne, closureCheckTwo, finish, yes, no
    }

    private static final Logger log = Logger
            .getLogger("aprove.verification.dpframework.TRSProblem.Utility.LoopFinder");

    public LoopFinder(final ImmutableSet<Rule> R) {
        // default-values for the methods copied from the NonTerminationProcessor
        this(R, Heuristic.NORMAL, 3, 3, 3);
    }

    public LoopFinder(final ImmutableSet<Rule> R, final Heuristic heuristic,
            final int totalLimit, final int rightLimit, final int leftLimit) {
        this.heuristic = heuristic;
        this.totalLimit = totalLimit;
        this.rightLimit = rightLimit;
        this.leftLimit = leftLimit;

        final QTRSProblem qtrs = QTRSProblem.create(R);
        this.initialize(qtrs);
    }

    /**
     * If constructed with a QTRSProblem, the LoopFinder will only return loops
     * that respect Q.
     */
    public LoopFinder(final QTRSProblem qtrs, final Heuristic heuristic, final int totalLimit, final int rightLimit,
            final int leftLimit) {
        this.heuristic = heuristic;
        this.totalLimit = totalLimit;
        this.rightLimit = rightLimit;
        this.leftLimit = leftLimit;

        this.initialize(qtrs);
    }

    /**
     * prepare for the search for (QDP-/TRS-)Loops
     */
    private void initialize(QTRSProblem qtrs) {
        // get the Dependency Pairs of the QTRSProblem "qtrs"
        final ImmutableTriple<ImmutableSet<Rule>, ImmutableMap<FunctionSymbol, FunctionSymbol>, ImmutableMap<Rule, List<Pair<Position, Rule>>>> dps = qtrs
                .getDPs();
        final ImmutableSet<Rule> dpRules = dps.x;
        final ImmutableMap<FunctionSymbol, FunctionSymbol> defToTup = dps.y;
        final ImmutableMap<Rule, List<Pair<Position, Rule>>> mapRruleToDp = dps.z;

        // we have to map Tuple-Symbols to their original Functions-Symbols,
        //      so reverse "defToTup" to "tupToDef"
        final HashMap<FunctionSymbol, FunctionSymbol> tupToDef = new HashMap<FunctionSymbol, FunctionSymbol>();
        final Set<Map.Entry<FunctionSymbol, FunctionSymbol>> defToTupSet = defToTup
                .entrySet();
        for (final Map.Entry<FunctionSymbol, FunctionSymbol> defTup : defToTupSet) {
            tupToDef.put(defTup.getValue(), defTup.getKey());
        }

        // we have to map Dependency Pairs to their original TRS-Rules (+ Positions),
        //      so reverse "mapRruleToDp" to "mapDpToRrule"
        final HashMap<Rule, HashSet<Pair<Rule, Position>>> mapDpToRrule = this
                .reverse(mapRruleToDp);

        // make a QDPProblem from our QTRSProblem as input for the method copied from the NonTerminationProcessor
        final QDPProblem qdpProblem = QDPProblem.create(dpRules, qtrs, true);

        // now feed the methods copied from the NonTerminationProcessor with the QDPProblem
        this.nonTermProc = new NonTerminationProcedure(qdpProblem,
                mapDpToRrule, tupToDef);
    }

    public Set<Loop> getLoops(final Abortion aborter) throws AbortionException {
        final Set<Loop> result = this.nonTermProc.getLoops(aborter);

        if (result != null) {
            // check the Loops for Soundness and return Null if an Error occurs
            for (final Loop actLoop : result) {
                if (!actLoop.check()) {
                    LoopFinder.log
                            .info("A Loop in the LoopFinder was not checked properly, so no Loops are returned. :/\n");

                    return null;
                }
            }
        }

        return result;
    }

    /**
     * reverse "mapRruleToDp" to "mapDpToRrule"
     */
    private HashMap<Rule, HashSet<Pair<Rule, Position>>> reverse(
            final ImmutableMap<Rule, List<Pair<Position, Rule>>> mapRruleToDp) {
        final HashMap<Rule, HashSet<Pair<Rule, Position>>> mapDpToRrule = new HashMap<Rule, HashSet<Pair<Rule, Position>>>();
        final Set<Map.Entry<Rule, List<Pair<Position, Rule>>>> mapRruleToDpSet = mapRruleToDp
                .entrySet();
        for (final Map.Entry<Rule, List<Pair<Position, Rule>>> actPairEntry : mapRruleToDpSet) {
            final Rule actRrule = actPairEntry.getKey();
            final List<Pair<Position, Rule>> actDpList = actPairEntry
                    .getValue();
            for (final Pair<Position, Rule> posDp : actDpList) {
                final Rule actDp = posDp.y;
                final Position actPos = posDp.x;
                if (mapDpToRrule.containsKey(actDp)) {
                    final HashSet<Pair<Rule, Position>> actRruleSet = mapDpToRrule
                            .get(actDp);
                    actRruleSet.add(new Pair<Rule, Position>(actRrule, actPos));
                } else {
                    final HashSet<Pair<Rule, Position>> actRruleSet = new HashSet<Pair<Rule, Position>>();
                    actRruleSet.add(new Pair<Rule, Position>(actRrule, actPos));
                    mapDpToRrule.put(actDp, actRruleSet);
                }
            }
        }

        return mapDpToRrule;
    }

    //********************************************************************************************************************
    // Help- (and some new) Methods and -Attributes copied and adjusted from the NonTerminationProcessor to find QDP-Loops
    //********************************************************************************************************************

    public static enum Heuristic {
        NORMAL, // standard heuristic which uses backward or forward narrowing
        // and sometimes performs narrowing into variables
        ONLY_FORWARD_NARROWING
        // only do forward narrowing where narrowing into variables is NOT
        // allowed (sufficient for outermost transformation)
    }

    private static enum Direction {
        LEFT, RIGHT, NONE
    }

    private static enum Trs {
        P, R
    }

    /**
     * maximal number of narrowings with one rule
     */
    private final int totalLimit;
    /**
     * maximal number of narrowings to the left with one rule (to be more
     * precise with rule^{-1})
     */
    private final int leftLimit;
    /**
     * maximal number of narrowings to the right with one rule
     */
    private final int rightLimit;
    /**
     * heuristic which controls whether to narrow into variables, which
     * direction first, ...
     */
    private final Heuristic heuristic;

    /**
     * Class which encapsulates the procedure to check nontermination with
     * narrowing and semiunification.
     *
     * @author Matthias Sondermann
     */
    private class NonTerminationProcedure {

        // NEW
        /**
         * needed to keep track of the search for QDP-Loops
         */
        private LoopFinder.Status statusProcess, statusClosureCheck,
                statusActNarrowedPairsCheck;

        private Iterator<Rule> pCheckIterator;

        private Pair<Direction, Direction> directionOrder;

        private int actLimit;
        private List<NarrowPair> closure;
        private Set<Pair<TRSTerm, TRSTerm>> done;
        private NarrowPair actPair;
        private List<NarrowPair> newNarrowedPairs;
        private Iterator<NarrowPair> actNarrowedPairsCheckIterator;

        private final HashMap<Rule, HashSet<Pair<Rule, Position>>> mapDpToRrule;
        private final HashMap<FunctionSymbol, FunctionSymbol> tupToDef;

        // NEW-END -------------

        /**
         * given qdpProblem
         */
        private final QDPProblem qdpProblem;
        /**
         * map from function symbol to rule to avoid stupid unification checks
         */
        Map<FunctionSymbol, ImmutableSet<Rule>> rRuleMap;
        Map<FunctionSymbol, ImmutableSet<Rule>> rReverseRuleMap;
        /**
         * sets which are used for doing closure steps and remembering already
         * checked pairs
         */
        private List<NarrowPair> rulesFromPtoCheck;
        private Set<Pair<TRSTerm, TRSTerm>> rulesFromPalreadyChecked;
        /**
         * the sets of the original trs-rules, the given dependency pairs and
         * the union of them
         */
        private ImmutableSet<Rule> rRules;
        private ImmutableSet<Rule> pRules;
        private ImmutableSet<Rule> rReversedRules;
        private Set<Rule> allRules;
        /**
         * some flags which influence the heuristic or depend on it
         */
        private boolean narrowInVars;
        private boolean rightLinear;
        private boolean leftLinear;
        /**
         * actual total limit which is updated after narrowing in one direction
         * terminated
         */
        private int actualTotalLimit;
        private final boolean qIsNonEmpty;
        /**
         * if we have a SRS it suffices to narrow with matching instead of
         * semiunification
         */
        private final boolean matchingSuffices;

        // RENEWED
        public NonTerminationProcedure(
                final QDPProblem qdpProblem,
                final HashMap<Rule, HashSet<Pair<Rule, Position>>> mapDpToRrule,
                final HashMap<FunctionSymbol, FunctionSymbol> tupToDef) {
            this.qdpProblem = qdpProblem;
            this.rRuleMap = qdpProblem.getRwithQ().getRuleMap();
            this.rReverseRuleMap = qdpProblem.getRwithQ().getReverseRuleMap();
            this.actualTotalLimit = LoopFinder.this.totalLimit;
            this.qIsNonEmpty = !qdpProblem.getQ().isEmpty();

            // NEW
            this.mapDpToRrule = mapDpToRrule;
            this.tupToDef = tupToDef;

            // check if it suffices to narrow with matching and not with
            // semiunification
            this.matchingSuffices = this.qdpProblem.getMaxArity() == 1 ? true
                    : false;

            // NEW
            this.initialize();
        }

        /**
         * prepare for the search for QDP-Loops
         */
        public void initialize() {
            // get rules of R and P
            this.rRules = this.qdpProblem.getR();
            this.pRules = this.qdpProblem.getP();

            // fill rReversedRule set
            HashSet<Rule> dummy = new HashSet<Rule>();
            for (final Set<Rule> value : this.rReverseRuleMap.values()) {
                dummy.addAll(value);
            }
            this.rReversedRules = ImmutableCreator.create(dummy);
            dummy = null;

            // fill the set this.allRules
            this.allRules = new LinkedHashSet<Rule>();
            this.allRules.addAll(this.rRules);
            this.allRules.addAll(this.pRules);

            // check left and right linearity
            this.leftLinear = aprove.verification.dpframework.BasicStructures.CollectionUtils
                    .isLeftLinear(this.allRules);
            this.rightLinear = aprove.verification.dpframework.BasicStructures.CollectionUtils
                    .isRightLinear(this.allRules);

            // initial closure step with dependency pairs
            this.rulesFromPtoCheck = new ArrayList<NarrowPair>();
            this.rulesFromPalreadyChecked = new LinkedHashSet<Pair<TRSTerm, TRSTerm>>();

            this.statusProcess = LoopFinder.Status.pRulesCheck;
        }

        /**
         * search for a QDP-Loop and get the corresponding TRS-Loops from it;
         *
         * there is PURPOSELY no "break" in the outer "switch"-method !
         *      (because this method controls the search-flow)
         */
        public Set<Loop> getLoops(final Abortion aborter)
                throws AbortionException {
            switch (this.statusProcess) {
                case pRulesCheck:
                    if (this.pCheckIterator == null) {
                        this.pCheckIterator = this.pRules.iterator();
                    }

                    // if a pair semiunifies this will be the matcher and the
                    // semiunifier
                    Pair<TRSSubstitution, TRSSubstitution> subst;

                    Rule dp;

                    // first add all needed pRules to the dp sets

                    while (this.pCheckIterator.hasNext()) {
                        dp = this.pCheckIterator.next();

                        final NarrowPair newPair = new NarrowPair(dp,
                                this.allRules);
                        // check dp only if it wasn't already checked earlier
                        // (use standard representation to avoid adding two pairs which
                        // are equal under variable renaming
                        if (!this.rulesFromPalreadyChecked.contains(newPair
                                .getStandardRepresentation())) {
                            // is the pair semiunifiable?
                            subst = this.testPair(newPair, aborter);
                            if (subst != null) {
                                // UPDATE !!
                                /*
                                this.rulesFromPalreadyChecked.add(newPair
                                        .getStandardRepresentation());
                                */

                                // since a semiunifiable pair is found nontermination is
                                // proved and so nothing more is to do
                                return this.getLoops(newPair, subst);
                            }
                            // add newPair to narrow it later
                            this.rulesFromPtoCheck.add(newPair);
                            // never add this pair again (and no pair which is equal to
                            // this one under variable renaming)
                            this.rulesFromPalreadyChecked.add(newPair
                                    .getStandardRepresentation());
                        }
                    }

                    // create heuristic order of narrowing directions
                    switch (LoopFinder.this.heuristic) {
                        case ONLY_FORWARD_NARROWING:
                            this.directionOrder = new Pair<Direction, Direction>(
                                    Direction.RIGHT, Direction.NONE);
                            this.narrowInVars = false;
                            break;
                        case NORMAL:
                            // if P united with R is left-linear: first narrow backwards
                            if (this.leftLinear) {
                                this.directionOrder = new Pair<Direction, Direction>(
                                        Direction.LEFT, Direction.RIGHT);
                            }
                            // if P united with R is right-linear: first narrow forwards
                            else if (this.rightLinear) {
                                this.directionOrder = new Pair<Direction, Direction>(
                                        Direction.RIGHT, Direction.LEFT);
                            }
                            // if P united with R is not left-linear and not
                            // right-linear: first narrow backwards and narrow into
                            // variables
                            else {
                                this.directionOrder = new Pair<Direction, Direction>(
                                        Direction.LEFT, Direction.RIGHT);
                                this.narrowInVars = true;
                                // because narrowing in variables is a lot of work
                                this.actualTotalLimit = 1;
                            }
                            break;
                        default:
                            throw new RuntimeException(
                                    "Unknown heuristic specified in non-termination procedure");
                    }

                    // do closure steps in both directions, first into directionOrder.x
                    // and after that into directionOrder.y

                    this.statusProcess = LoopFinder.Status.closureCheckOne;
                    this.statusClosureCheck = LoopFinder.Status.no;
                case closureCheckOne:
                    // narrow to the first direction
                    final Pair<NarrowPair, Pair<TRSSubstitution, TRSSubstitution>> dummyPairOne;

                    dummyPairOne = this.doClosure(this.directionOrder.x,
                            aborter);
                    if (dummyPairOne != null) {
                        return this.getLoops(dummyPairOne.x, dummyPairOne.y);
                    }

                    // since the narrowing to the first direction took place the total
                    // limit has to be updated
                    if (this.directionOrder.x == Direction.LEFT) {
                        this.actualTotalLimit -= LoopFinder.this.leftLimit;
                    } else {
                        this.actualTotalLimit -= LoopFinder.this.rightLimit;
                    }
                    if (this.actualTotalLimit <= 0
                            || this.directionOrder.y == Direction.NONE) {
                        // nothing more to do and we haven't found a QDP-Loop with this applLimit
                        this.statusProcess = LoopFinder.Status.finish;

                        return null;
                    }

                    this.statusProcess = LoopFinder.Status.closureCheckTwo;
                    this.statusClosureCheck = LoopFinder.Status.no;
                case closureCheckTwo:
                    // if narrowing to the first direction failed now narrow to the
                    // second direction
                    final Pair<NarrowPair, Pair<TRSSubstitution, TRSSubstitution>> dummyPairTwo;

                    dummyPairTwo = this.doClosure(this.directionOrder.y,
                            aborter);
                    if (dummyPairTwo != null) {
                        return this.getLoops(dummyPairTwo.x, dummyPairTwo.y);
                    }

                    this.statusProcess = LoopFinder.Status.finish;
                case finish:
                    return null;
                default:
                    throw new RuntimeException(
                            "Unknown QDP-Loop-Search-Status specified in non-termination procedure");
            }
        }

        /**
         * Do narrowings in direction <code>actDir</code> until a pair which
         * semiunifies is found or the limit is reached.
         */
        private Pair<NarrowPair, Pair<TRSSubstitution, TRSSubstitution>> doClosure(
                final Direction actDir, final Abortion aborter)
                throws AbortionException {

            if (this.statusClosureCheck == LoopFinder.Status.no) {
                // set the actual limit depending on the direction
                if (this.directionOrder.x == Direction.RIGHT) {
                    this.actLimit = LoopFinder.this.rightLimit;
                } else {
                    this.actLimit = LoopFinder.this.leftLimit;
                }

                // some needed stuff
                this.closure = new ArrayList<NarrowPair>();
                this.closure.addAll(this.rulesFromPtoCheck);

                this.done = new LinkedHashSet<Pair<TRSTerm, TRSTerm>>();
                this.done.addAll(this.rulesFromPalreadyChecked);

                this.statusClosureCheck = LoopFinder.Status.yes;
                this.statusActNarrowedPairsCheck = LoopFinder.Status.no;
            }

            // do more closure steps as long as new narrow-pairs result out of
            // narrowing.
            // take every element which was added to and never removed from
            // closure list
            while (!this.closure.isEmpty()) {
                if (this.statusActNarrowedPairsCheck == LoopFinder.Status.no) {
                    aborter.checkAbortion();
                    // get a custom narrow pair (take wlog the first one)
                    this.actPair = this.closure.get(0);
                    this.newNarrowedPairs = new ArrayList<NarrowPair>();
                    // try to narrow pair with every rule and get all new narrow
                    // pairs

                    if (this.actNarrowedPairsCheckIterator == null
                            || !this.actNarrowedPairsCheckIterator.hasNext()) {
                        this.actNarrowedPairsCheckIterator = this
                                .doOneNarrowingStep(this.actPair, actDir,
                                        this.actLimit, aborter).iterator();
                    }

                    this.statusActNarrowedPairsCheck = LoopFinder.Status.yes;
                }

                // add all new narrow pairs which have not been computed yet

                // some needed stuff
                Pair<TRSSubstitution, TRSSubstitution> subst = null;

                NarrowPair actNewPair;

                while (this.actNarrowedPairsCheckIterator.hasNext()) {
                    actNewPair = this.actNarrowedPairsCheckIterator.next();

                    // check this pair only if it or a pair that is equal to
                    // this except by variable renaming was never checked before
                    if (!this.done.contains(actNewPair
                            .getStandardRepresentation())) {
                        // is the new pair semiunifiable?
                        subst = this.testPair(actNewPair, aborter);
                        if (subst != null) {
                            // UPDATE
                            // never add this pair again
                            /*
                            this.done.add(actNewPair
                                    .getStandardRepresentation());
                            */

                            // nontermination proved so nothing more is to do
                            return new Pair<NarrowPair, Pair<TRSSubstitution, TRSSubstitution>>(
                                    actNewPair, subst);
                        }
                        // this pair has to be narrowed later
                        this.newNarrowedPairs.add(actNewPair);
                        // never add this pair again
                        this.done.add(actNewPair.getStandardRepresentation());
                    }
                }

                this.statusActNarrowedPairsCheck = LoopFinder.Status.no;

                // add all new narrow pairs to the closure list
                this.closure.addAll(this.newNarrowedPairs);
                // actPair will never be touched again
                this.closure.remove(this.actPair);
            }
            // closure list is empty and no semiunification succeded
            // so nontermination could not be proved with this applLimit
            return null;
        }

        /**
         * adapted and adjusted from the NonTerminationProcessor ("printRewritingSequence")
         */
        private Set<Loop> getLoops(final NarrowPair narrowPair,
                final Pair<TRSSubstitution, TRSSubstitution> subst) {

            Set<Loop> result = new HashSet<Loop>();

            final TRSSubstitution matcher = subst.x;
            final TRSSubstitution semiUnifier = subst.y;

            final TRSTerm dpLhs = narrowPair.dp.getLeft();

            List<Triple<Rule, Position, Trs>> narrowList = narrowPair
                    .getNarrowList();

            // if the dp directly semiunifies nothing is to check
            if (narrowList.isEmpty()) {
                // "The DP semiunifies directly so there is only one rewrite step from "
                // + dpLhs.applySubstitution(semiUnifier) + " to " +
                // dpRhs.applySubstitution(semiUnifier)
                final Loop loop = new Loop();
                loop.getTerms()
                        .add(
                                this.replaceLeadingTupleSymbol(dpLhs
                                        .applySubstitution(semiUnifier),
                                        this.tupToDef));
                result.addAll(this.branche(loop, this.mapDpToRrule
                        .get(narrowPair.dp), Position.create()));
            } else {
                final Direction dir = narrowPair.narrowDir;

                // check narrowing direction to know how to narrow
                // forward narrowing: start with rhs of the initial dp and narrow up to
                // pair.y
                if (dir == Direction.RIGHT) {
                    final Loop loop = new Loop();
                    loop.getTerms().add(
                            this.replaceLeadingTupleSymbol(narrowPair.x
                                    .applySubstitution(semiUnifier),
                                    this.tupToDef));
                    result.addAll(this.branche(loop, this.mapDpToRrule
                            .get(narrowPair.dp), Position.create()));
                }
                // backward narrowing: start with pair.x and narrow up to the lhs of the
                // initial dp
                else {
                    final Loop loop = new Loop();
                    loop.getTerms().add(
                            this.replaceLeadingTupleSymbol(narrowPair.x
                                    .applySubstitution(semiUnifier),
                                    this.tupToDef));
                    result.add(loop);

                    // reverse the list to get the forward narrowing steps
                    final List<Triple<Rule, Position, Trs>> dummyList = new ArrayList<Triple<Rule, Position, Trs>>();
                    for (final Triple<Rule, Position, Trs> rTriple : narrowList) {
                        dummyList.add(0, rTriple);
                    }
                    narrowList = dummyList;
                }

                // both cases (forward and backward narrowing) are equal now

                Rule actRule;
                Position actPos;

                // check the whole narrowing list
                for (final Triple<Rule, Position, Trs> actTriple : narrowList) {
                    actRule = actTriple.x;
                    actPos = actTriple.y;
                    final Trs actTrs = actTriple.z;

                    if (actTrs == Trs.R) {
                        for (final Loop actLoop : result) {
                            this.add(actLoop, actRule, actPos, Position
                                    .create());
                        }
                    }

                    if (actTrs == Trs.P) {
                        result = (this.branche(result, this.mapDpToRrule
                                .get(actRule), Position.create()));
                    }
                }

                if (dir == Direction.LEFT) {
                    result = (this.branche(result, this.mapDpToRrule
                            .get(narrowPair.dp), Position.create()));
                }
            }

            /*
             * add the Matcher for the instance of the first term of a loop in
             *      the last term of a loop to each TRS-Loop;
             * this Matcher will be the same for each TRS-Loop
             *      (= the Matcher of the corresponding Semi-Unification-Problem)
             */
            for (final Loop actLoop : result) {
                actLoop.setMatcher(matcher);
            }

            return result;
        }

        /**
         * needed to build a TRS-Loop; side-effects on parameter "loop"
         */
        private void add(final Loop loop, Rule rule, Position redPos,
                final Position contextStep) {
            final Position pos = loop.getPosition();

            redPos = pos.append(redPos);
            final TRSTerm last = loop.getLast();
            final TRSTerm subTerm = last.getSubterm(redPos);
            final Set<TRSVariable> varsLast = last.getVariables();
            rule = rule.renameVariables(varsLast);
            final TRSTerm lhs = rule.getLeft();
            final TRSTerm rhs = rule.getRight();
            final TRSSubstitution redMa = lhs.getMatcher(subTerm);
            final TRSTerm newTerm = last.replaceAt(redPos, rhs
                    .applySubstitution(redMa));

            loop.getTerms().add(newTerm);
            loop.getRules().add(rule);
            loop.getPositions().add(redPos);
            loop.getSubstitutions().add(redMa);

            loop.setPosition(pos.append(contextStep));
        }

        /**
         * similar to the method above, but for a Set of rules
         */
        private Set<Loop> branche(final Loop loop,
                final Set<Pair<Rule, Position>> redRulesContextSteps,
                final Position redPos) {
            final HashSet<Loop> result = new HashSet<Loop>();

            Loop copy;

            for (final Pair<Rule, Position> redRuleContextStep : redRulesContextSteps) {
                copy = loop.shallowCopy();
                this.add(copy, redRuleContextStep.x, redPos,
                        redRuleContextStep.y);
                result.add(copy);
            }

            return result;
        }

        /**
         * similar to the method above, but for a Set of initial loops
         */
        private Set<Loop> branche(final Set<Loop> loops,
                final Set<Pair<Rule, Position>> redRulesContextSteps,
                final Position redPos) {
            final HashSet<Loop> result = new HashSet<Loop>();

            for (final Loop actLoop : loops) {
                result.addAll(this.branche(actLoop, redRulesContextSteps,
                        redPos));
            }

            return result;
        }

        private TRSTerm replaceLeadingTupleSymbol(final TRSTerm t,
                final HashMap<FunctionSymbol, FunctionSymbol> tupToDef) {
            if (t instanceof TRSFunctionApplication) {
                final TRSFunctionApplication tFuncApp = (TRSFunctionApplication) t;

                final FunctionSymbol newRoot = tupToDef.get(tFuncApp
                        .getRootSymbol());

                if (newRoot != null) {
                    return TRSTerm.createFunctionApplication(newRoot, tFuncApp
                            .getArguments());
                }
            }

            return t;
        }

        /**
         * Generates every possible narrowing out of the given pair with
         * direction <code>actDir</code>
         *
         * @param narrowingPair
         *            original pair which is to narrow
         * @return every possible narrowing of <code>narrowingPair</code>
         */
        private Set<NarrowPair> doOneNarrowingStep(final NarrowPair actPair,
                final Direction actDir, final int dirLimit,
                final Abortion aborter) throws AbortionException {

            final Set<NarrowPair> newNarrowedPairs = new LinkedHashSet<NarrowPair>();
            final TRSTerm left = actPair.x;
            final TRSTerm right = actPair.y;

            // first get the correct terms depending on the direction
            TRSTerm toBeNarrowed = null;
            TRSTerm notToBeNarrowed = null;
            Set<TRSVariable> termVars = null;
            if (actDir == Direction.LEFT) {
                toBeNarrowed = left;
                notToBeNarrowed = right;
                termVars = left.getVariables();
            } else {
                toBeNarrowed = right;
                notToBeNarrowed = left;
                termVars = right.getVariables();
            }

            // if the actual term is a variable and we do not narrow into
            // variables nothing is to do
            if (toBeNarrowed.isVariable() && !this.narrowInVars) {
                return newNarrowedPairs;
            }

            // try to narrow with every rule from P at position epsilon
            for (Rule actPrule : this.pRules) {
                // if this rule was used to often continue with next rule
                if (this.actualTotalLimit >= 0
                        && this.actualTotalLimit <= actPair
                                .getNrOfAppls(actPrule)) {
                    continue;
                }
                if (dirLimit >= 0 && dirLimit <= actPair.getNrOfAppls(actPrule)) {
                    continue;
                }

                // variables of rule and subterm have to be disjoint
                actPrule = actPrule.renameVariables(termVars);

                TRSTerm l = null;
                TRSTerm r = null;
                if (actDir == Direction.LEFT) {
                    l = actPrule.getRight();
                    r = actPrule.getLeft();
                } else {
                    l = actPrule.getLeft();
                    r = actPrule.getRight();
                }
                // try to unify toBeNarrowed and actual dp
                final TRSSubstitution actMgu = l.getMGU(toBeNarrowed);
                if (actMgu != null) {
                    // possible narrowing found so do it!
                    // do we have to forbid that because of Q?

                    // check if the lhs of the P-term is Q-normal
                    if (this.qdpProblem.getQ().canBeRewritten(toBeNarrowed)) {
                        continue;
                    }
                    final TRSTerm newToBeNarrowed = r.applySubstitution(actMgu);
                    final TRSTerm newNotToBeNarrowed = notToBeNarrowed
                            .applySubstitution(actMgu);

                    // create new narrowing pair depending on the direction and
                    // add it to the return set
                    if (actDir == Direction.LEFT) {
                        final NarrowPair newNarrowingPair = new NarrowPair(
                                newToBeNarrowed, newNotToBeNarrowed, actPair,
                                new Triple<Rule, Position, Trs>(actPrule,
                                        Position.create(), Trs.P), actDir);
                        newNarrowedPairs.add(newNarrowingPair);
                    } else {
                        final NarrowPair newNarrowingPair = new NarrowPair(
                                newNotToBeNarrowed, newToBeNarrowed, actPair,
                                new Triple<Rule, Position, Trs>(actPrule,
                                        Position.create(), Trs.P), actDir);
                        newNarrowedPairs.add(newNarrowingPair);
                    }
                }
            }

            // now try to narrow with every trs rule at every (non variable)
            // position
            // iterate over all subterms of termToNarrow
            final Collection<Pair<Position, TRSTerm>> posWithSubterm = toBeNarrowed
                    .getPositionsWithSubTerms();
            for (final Pair<Position, TRSTerm> actPosTermPair : posWithSubterm) {

                // check every trs rule at every (non variable) position
                final Position actPos = actPosTermPair.x;
                final TRSTerm actSubterm = actPosTermPair.y;

                Set<Rule> neededRules = new LinkedHashSet<Rule>();

                // check if we want to narrow in variables
                if (actSubterm.isVariable()) {
                    if (this.narrowInVars) {
                        // every rule is a candidate
                        if (actDir == Direction.RIGHT) {
                            neededRules = this.rRules;

                        } else {
                            neededRules = this.rReversedRules;
                        }
                    } else {
                        // nothing to do
                        continue;
                    }
                } else {
                    // actSubterm is a function application
                    // now check every rule for narrowing with a useful root
                    // symbol
                    if (actDir == Direction.RIGHT) {
                        final FunctionSymbol fs = ((TRSFunctionApplication) actSubterm)
                                .getRootSymbol();
                        final ImmutableSet<Rule> actRRules = this.rRuleMap
                                .get(fs);
                        if (actRRules != null) {
                            neededRules.addAll(actRRules);
                        }
                    } else {
                        final FunctionSymbol fs = ((TRSFunctionApplication) actSubterm)
                                .getRootSymbol();
                        final ImmutableSet<Rule> actRRevRules = this.rReverseRuleMap
                                .get(fs);
                        if (actRRevRules != null) {
                            neededRules.addAll(actRRevRules);
                        }
                        final Collection<Rule> rulesWithVarRhs = this.qdpProblem
                                .getRwithQ().getCollapsingRules();
                        neededRules.addAll(rulesWithVarRhs);
                    }
                }

                for (Rule actRule : neededRules) {
                    aborter.checkAbortion();
                    // if this rule was used to often continue with next rule
                    if (this.actualTotalLimit >= 0
                            && this.actualTotalLimit <= actPair
                                    .getNrOfAppls(actRule)) {
                        continue;
                    }
                    if (dirLimit >= 0
                            && dirLimit <= actPair.getNrOfAppls(actRule)) {
                        continue;
                    }

                    // variables of rule and subterm have to be disjoint
                    actRule = actRule.renameVariables(termVars);

                    // now get the right terms depending on the direction
                    // l standes for the term which is used for unification, r
                    // for the other one
                    // so don't be confused with the names l and r
                    TRSTerm l = null;
                    TRSTerm r = null;
                    if (actDir == Direction.LEFT) {
                        l = actRule.getRight();
                        r = actRule.getLeft();
                    } else {
                        l = actRule.getLeft();
                        r = actRule.getRight();
                    }

                    // try to unify toBeNarrowed.subTerm and actual rule
                    final TRSSubstitution actMgu = l.getMGU(actSubterm);
                    if (actMgu != null) {
                        // possible narrowing found so do it!
                        // do we have to forbid that because of Q?

                        // check if every non variable subterm is Q-normal
                        if (this.qdpProblem.getQ().canBeRewrittenBelowRoot(
                                actSubterm)) {
                            continue;
                        }
                        final TRSTerm newToBeNarrowed = toBeNarrowed.replaceAt(
                                actPos, r).applySubstitution(actMgu);
                        final TRSTerm newNotToBeNarrowed = notToBeNarrowed
                                .applySubstitution(actMgu);

                        // create new narrowing pair depending on the direction
                        // and add it to the return set
                        if (actDir == Direction.LEFT) {
                            final NarrowPair newNarrowingPair = new NarrowPair(
                                    newToBeNarrowed, newNotToBeNarrowed,
                                    actPair, new Triple<Rule, Position, Trs>(
                                            actRule, actPos, Trs.R), actDir);
                            newNarrowedPairs.add(newNarrowingPair);
                        } else {
                            final NarrowPair newNarrowingPair = new NarrowPair(
                                    newNotToBeNarrowed, newToBeNarrowed,
                                    actPair, new Triple<Rule, Position, Trs>(
                                            actRule, actPos, Trs.R), actDir);
                            newNarrowedPairs.add(newNarrowingPair);
                        }

                    }
                }
            }
            return newNarrowedPairs;
        }

        /**
         * Tests a narrowing pair if <code>pair.x</code> and <code>pair.y</code>
         * semiunify.
         *
         * @return true iff the pair semiunifies
         */
        private Pair<TRSSubstitution, TRSSubstitution> testPair(
                final NarrowPair pair, final Abortion aborter)
                throws AbortionException {
            Pair<TRSSubstitution, TRSSubstitution> subst = null;

            if (this.matchingSuffices) {
                // in case of a SRS it suffices to check if terms match
                final TRSSubstitution matcher = pair.x.getMatcher(pair.y);
                if (matcher != null) {
                    subst = new Pair<TRSSubstitution, TRSSubstitution>(pair.x
                            .getMatcher(pair.y),
                            TRSSubstitution.EMPTY_SUBSTITUTION);
                }
            } else {
                subst = pair.x.getSemiSubstitutions(pair.y);
            }
            // check if these terms semiunify
            if(subst!=null){
                if(this.qIsNonEmpty) {
                    NarrowPair checkPair = pair.copy();
                    // if we have to check the innermost case we have to check wether all narrowings were innermost steps
                    if(!this.testQcondition(checkPair,subst)) {
                       // if not all steps were innermost go on with the closure procedure
                       return null;
                    }
                }
                // return matcher and semiUnifier as a pair
                return subst;
            }
            return subst;
        }

        /**
         * given a redex problem (t,mu,q), this procedure will add
         * all non-variable subterms of t and {x\mu | x in Vars(t,t mu, t mu^2, ...)}
         * to the redexes set
         * @param t
         * @param mu
         * @param redexes
         */
        private void addToRedexSub(final TRSTerm t, TRSSubstitution mu, Set<TRSTerm> redexes) {
            Set<TRSVariable> vars = t.getVariables();
            TRSTerm tmui = t;
            do {
                tmui = tmui.applySubstitution(mu);
            } while (vars.addAll(tmui.getVariables()));
            // okay, now we know that we will not see new variables any more
            redexes.addAll(t.getNonVariableSubTerms());
            for (TRSVariable x : vars) {
                redexes.addAll(x.applySubstitution(mu).getNonVariableSubTerms());
            }
        }

        /**
         * Checks wether all rewritings of <code>pair</code> are Q-restricted steps.
         * Let mu be the matcher from the semiunification.
         *
         * @return true iff all steps are innermost steps w.r.t. Q
         */
        private boolean testQcondition(NarrowPair pair, Pair<TRSSubstitution,TRSSubstitution> substPair){
            /* if(log.isLoggable(Level.FINE)) {
                log.log(Level.FINE , "NontermProcedure " + this.procNumber + ": Start Q-check with " + pair + " and " + substPair + "\n");
            } */
            TRSSubstitution matcher = substPair.x;
            TRSSubstitution semiunifier = substPair.y;

            /*
             * first get all redexes of the rewriting sequence
             */
            List<Pair<TRSFunctionApplication,Trs>> redexList = this.getUsedRedexes(pair,semiunifier);

            /*
             * then create the set of lhss of matching problems
             */
            Set<TRSTerm> forMatching = new LinkedHashSet<TRSTerm>();

            for (Pair<TRSFunctionApplication,Trs> termTrs : redexList) {
                TRSFunctionApplication redex = termTrs.x;
                if (termTrs.y == Trs.P) {
                    this.addToRedexSub(redex, matcher, forMatching);
                } else {
                    for (TRSTerm redexSub : redex.getArguments()) {
                        this.addToRedexSub(redexSub, matcher, forMatching);
                    }
                }
            }

            /*
             * now identify increasing vars to be able to solve matching problems
             */
            Set<TRSVariable> increasing = new HashSet<TRSVariable>();
            Map<TRSVariable,TRSVariable> nonIncreasing = new LinkedHashMap<TRSVariable,TRSVariable>();
            final Map<TRSVariable, ? extends TRSTerm> mu = matcher.toMap();
            for (Map.Entry<TRSVariable, ? extends TRSTerm> xt : mu.entrySet()) {
                if (xt.getValue().isVariable()) {
                    nonIncreasing.put(xt.getKey(),(TRSVariable)xt.getValue());
                } else {
                    increasing.add(xt.getKey());
                }
            }
            boolean change = true;
            while (change) {
                change = false;
                Iterator<Map.Entry<TRSVariable, TRSVariable>> i = nonIncreasing.entrySet().iterator();
                while (i.hasNext()) {
                    Map.Entry<TRSVariable, TRSVariable> xy = i.next();
                    if (increasing.contains(xy.getValue())) {
                        increasing.add(xy.getKey());
                        i.remove();
                        change = true;
                    }
                }
            }


            /*
             * then transform matching problems into identity problems.
             * for each matching problem that can possibly be solved we generate one identity problem
             * in the set identProblems
             */
            Comparator<Pair<TRSTerm,TRSTerm>> matchComparator = new Comparator<Pair<TRSTerm,TRSTerm>>() {
                // second argument first (and variables last)
                // => pairs (t,f(..)) will be in front
                @Override
                public int compare(Pair<TRSTerm, TRSTerm> one, Pair<TRSTerm, TRSTerm> two) {
                    int cy = one.y.compareTo(two.y);
                    if (cy == 0) {
                        return one.x.compareTo(two.x);
                    } else {
                        return -cy;
                    }
                }
            };


            Queue<Pair<TRSTerm, TRSTerm>> matchingProblem = new PriorityQueue<Pair<TRSTerm,TRSTerm>>(5, matchComparator);
            Collection<Collection<Set<TRSTerm>>> identProblems = new LinkedHashSet<Collection<Set<TRSTerm>>>();
            for (TRSTerm qInit : this.qdpProblem.getQ().getTerms()) {
                sLoop: for (TRSTerm sInit : forMatching) {
                    matchingProblem.clear();
                    matchingProblem.offer(new Pair<TRSTerm, TRSTerm>(sInit,qInit));
                    while (!matchingProblem.isEmpty()) {
                        Pair<TRSTerm,TRSTerm> sq = matchingProblem.peek();
                        TRSTerm q = sq.y;
                        if (q.isVariable()) {
                            // we are done, so let us build identity problems
                            Map<TRSVariable,Set<TRSTerm>> ident = new HashMap<TRSVariable,Set<TRSTerm>>();
                            for (Pair<TRSTerm, TRSTerm> tx : matchingProblem) {
                                TRSVariable x = (TRSVariable) tx.y; // this cast must succeed since if there is some pair
                                                              // with non-variable in second component then it
                                                              // should be returned by peek() instead of sq!
                                TRSTerm t = tx.x;
                                Set<TRSTerm> tsForX = ident.get(x);
                                if (tsForX == null) {
                                    tsForX = new LinkedHashSet<TRSTerm>();
                                    ident.put(x, tsForX);
                                }
                                tsForX.add(t);
                            }
                            Collection<Set<TRSTerm>> tsThatMustBecomeIdentical = new LinkedHashSet<Set<TRSTerm>>();
                            for (Set<TRSTerm> tsForX : ident.values()) {
                                if (tsForX.size() > 1) {
                                    tsThatMustBecomeIdentical.add(tsForX);
                                }
                            }
                            if (tsThatMustBecomeIdentical.isEmpty()) {
                                return false; // matching problem solvable
                            }
                            identProblems.add(tsThatMustBecomeIdentical);
                            continue sLoop;
                        } else {
                            // apply some matching rule
                            TRSTerm s = sq.x;
                            if (s.isVariable()) {
                                if (increasing.contains(s)) {
                                    // apply rule (i) (apply mu on all lhss)
                                    Queue<Pair<TRSTerm, TRSTerm>> newMatchProblem = new PriorityQueue<Pair<TRSTerm,TRSTerm>>(matchingProblem.size(), matchComparator);
                                    matchingProblem.poll();
                                    do {
                                        sq.x = sq.x.applySubstitution(matcher);
                                        newMatchProblem.offer(sq);
                                        sq = matchingProblem.poll();
                                    } while (sq != null);
                                    matchingProblem = newMatchProblem;
                                } else {
                                    // apply rule (ii)
                                    continue sLoop;
                                }
                            } else {
                                TRSFunctionApplication fs = (TRSFunctionApplication) s;
                                TRSFunctionApplication gq = (TRSFunctionApplication) q;
                                if (fs.getRootSymbol().equals(gq.getRootSymbol())) {
                                    // apply rule (iv) (decompose)
                                    matchingProblem.poll();
                                    List<? extends TRSTerm> ss = fs.getArguments();
                                    List<? extends TRSTerm> qs = gq.getArguments();
                                    int i = 0;
                                    for (TRSTerm si : ss) {
                                        TRSTerm qi = qs.get(i);
                                        matchingProblem.offer(new Pair<TRSTerm,TRSTerm>(si, qi));
                                        i++;
                                    }
                                } else {
                                    // apply rule (iii)
                                    continue sLoop;
                                }
                            }
                        }
                    }
                    // solved form is empty matching problem
                    // which is trivially solvable
                    return false;
                }
            }

            /*
             * if all matching problems failed, do not compute cycle-free mu
             */
            if (identProblems.isEmpty()) {
                return true;
            }

            /*
             * finally solve identity problems
             * (whenever one identProblem in identProblems is solved then a matching problem is solved,
             *  to solve one identProblem for each set of terms tsForX one has to make all terms t mu^n equal,
             *  and by assumption all these sets tsForX have at least two terms)
             */

            /*
             *  step (i) of solving identity problems:
             *  find n >= 1 such that mu^n is acyclic.
             */

            int j = 2;
            BigInteger n = BigInteger.ONE;
            TRSSubstitution resMu = matcher;
            while (!nonIncreasing.isEmpty()) {
                Iterator<Map.Entry<TRSVariable, TRSVariable>> i = nonIncreasing.entrySet().iterator();
                while (i.hasNext()) {
                    Map.Entry<TRSVariable, TRSVariable> xv = i.next();
                    TRSVariable w = (TRSVariable) xv.getValue().applySubstitution(matcher);
                    if (w.equals(xv.getKey())) {
                        i.remove();
                        BigInteger m = n.multiply(BigInteger.valueOf(j)).divide(n.gcd(BigInteger.valueOf(j))); /* m = lcm(n, j) */
                        if (!n.equals(m)) {
                            int fact = m.divide(n).intValue(); // new factor
                            TRSSubstitution resMuHelp = resMu;
                            while (fact != 1) {
                                resMu = resMu.compose(resMuHelp);
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

            /*
             * now resMu is acyclic
             */

            idLoop: for (Collection<Set<TRSTerm>> identProblem : identProblems) {
                // first flatten to binary
                Set<Pair<TRSTerm,TRSTerm>> idProblems = new LinkedHashSet<Pair<TRSTerm,TRSTerm>>();
                for (Set<TRSTerm> tsForX : identProblem) {
                    for (TRSTerm t1 : tsForX) {
                        for (TRSTerm t2: tsForX) {
                            if (t1.compareTo(t2) > 0) { // in this way we won't have duplicate pairs
                                idProblems.add(new Pair<TRSTerm,TRSTerm>(t1,t2));
                            }
                        }
                    }
                }

                // if all identityProblems in idProblems can be solved, then we have a redex
                for (Pair<TRSTerm,TRSTerm> idProblem : idProblems) {
                    if (!this.identSolvable(resMu, idProblem.x, idProblem.y, increasing)) {
                        // this identProblem not solvable, so let's try next one
                        continue idLoop;
                    }
                }

                // all binary id-problems are solvable, so matching and hence redex problem solvalbe
                return false;
            }

            return true;
        }

        /**
         * decides whether the given identity problem is solvable.
         * @param mu has to be a cycle-free substitution!!! Hence, step (i) of the algorithm has to be done before.
         * @param s
         * @param t
         * @param increasing the set of increasing variables of mu
         */
        private boolean identSolvable(TRSSubstitution mu, TRSTerm s, TRSTerm t, Set<TRSVariable> increasing) {
            Set<TRSVariable> dom = mu.getDomain();


            // internal data structure: List< position p, s|_p, t|_p > such that everything above
            //                          the mentioned positions is identical
            Collection<Triple<Position,TRSTerm,TRSTerm>> workingList = new ArrayList<Triple<Position, TRSTerm, TRSTerm>>();
            Position p = Position.create();
            if (!this.decompose(p, s, t, increasing, dom, workingList)) {
                return false;
            }

            // step (ii)
            Map<TRSVariable,Collection<Triple<Position, TRSTerm, TRSTerm>>> S = new HashMap<TRSVariable, Collection<Triple<Position,TRSTerm,TRSTerm>>>();

            while (!workingList.isEmpty()) {
                Collection<Triple<Position,TRSTerm,TRSTerm>> newWorkingList = new ArrayList<Triple<Position, TRSTerm, TRSTerm>>();
                for (Triple<Position,TRSTerm,TRSTerm> pst : workingList) {
                    s = pst.y;
                    t = pst.z;
                    if (increasing.contains(s)) {
                        if (!this.addToS(pst, S)) { // step (vii)
                            return false; // step (viii)
                        }
                    }
                    if (increasing.contains(t)) {
                        if (!this.addToS(new Triple<Position,TRSTerm,TRSTerm>(pst.x, t, s), S)) { // step (vii)
                            return false; // step (viii)
                        }
                    }
                    // step (ix)
                    s = s.applySubstitution(mu);
                    t = t.applySubstitution(mu);
                    if (!this.decompose(pst.x, s, t, increasing, dom, newWorkingList)) {
                        return false;
                    }
                }

                workingList = newWorkingList; // step (x)
            }

            return true;
        }

        /**
         * adds the triple entry to S and returns false iff there is a conflict due to step (vii)
         * @param entry (the left term has to be an increasing variable, and the entry must be at a deepest position)
         * @param S
         */
        private boolean addToS(Triple<Position,TRSTerm,TRSTerm> entry, Map<TRSVariable,Collection<Triple<Position, TRSTerm, TRSTerm>>> S) {
            TRSVariable x = (TRSVariable) entry.y;
            Collection<Triple<Position, TRSTerm, TRSTerm>> xEntries = S.get(x);
            if (xEntries == null) {
                xEntries = new ArrayList<Triple<Position, TRSTerm, TRSTerm>>();
                xEntries.add(entry);
                S.put(x, xEntries);
            } else {
                TRSTerm u_2 = entry.z;
                Position p_2 = entry.x;
                for (Triple<Position, TRSTerm, TRSTerm> otherXEntry : xEntries) {
                    if (Globals.useAssertions) {
                        assert(!otherXEntry.equals(entry)) : "I thought that the set S cannot contain duplicates by construction. "+
                                                              "Either this is a bug in the construction of S or my thought was wrong.";
                    }
                    TRSTerm u_1 = otherXEntry.z;
                    Position p_1 = otherXEntry.x;
                    if (u_1.equals(u_2)) {
                        if (p_1.isPrefixOf(p_2)) {
                            // note that by assertion p_1 cannot be the same as p_2 at this point
                            // hence the check is a proper prefix check.
                            // Moreover, since the newly created entry is at a lowest position,
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
         * adds all (p',s|_p',t|_p') to todo such that
         * p' is below p,
         * p' is a deepest shared position,
         * s and t differ at position p'
         * all triples that are added may be solvable (if mu is defined accordingly)
         * (conflicts with (iv),(v),(vi) are detected)
         * @param p
         * @param s
         * @param t
         * @param increasing
         * @param dom
         * @param todo
         * @return false, if a conflict occurred, true otherwise.
         */
        private boolean decompose(Position p, TRSTerm s, TRSTerm t, Set<TRSVariable> increasing, Set<TRSVariable> dom, Collection<Triple<Position,TRSTerm,TRSTerm>> todo) {
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
                        return false; // step (v) (one can easily replace "notin Dom(mu)" by "not in increasing" in step (v))
                    }
                } else {
                    TRSFunctionApplication fs = (TRSFunctionApplication) s;
                    TRSFunctionApplication gt = (TRSFunctionApplication) t;
                    if (fs.getRootSymbol().equals(gt.getRootSymbol())) {
                        int i = 0; // step (iii) (on top level + decomposition)
                        List<? extends TRSTerm> ts = gt.getArguments();
                        for (TRSTerm si : fs.getArguments()) {
                            TRSTerm ti = ts.get(i);
                            Position pi = p.append(i);
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
         * Returns the list of all redexes of the rewriting sequence from pair.x to pair.y.
         */
        private List<Pair<TRSFunctionApplication,Trs>> getUsedRedexes(NarrowPair pair, TRSSubstitution semiunifier){
            List<Pair<TRSFunctionApplication,Trs>> redexList = new LinkedList<Pair<TRSFunctionApplication,Trs>>();
            List<Triple<Rule,Position,Trs>> narrowList = pair.getNarrowList();

            // if the dp directly semiunifies only the lhs of the dp is to check
            if(narrowList.isEmpty()){
                redexList.add(new Pair<TRSFunctionApplication,Trs>(((TRSFunctionApplication)pair.x).applySubstitution(semiunifier), Trs.P));
                return redexList;
            }

            Direction dir = pair.narrowDir;
            TRSTerm actTerm = pair.x.applySubstitution(semiunifier);
            // check narrowing direction to know how to narrow
            // forward narrowing: start with rhs of the initial dp and narrow up to pair.y
            if(dir==Direction.RIGHT){
                narrowList.add(0, new Triple<Rule,Position,Trs>(pair.dp, Position.create(),Trs.P));
            }
            // backward narrowing: start with pair.x and narrow up to the lhs of the initial dp
            else if(dir==Direction.LEFT){
                // reverse the list to get the forward narrowing steps
                List<Triple<Rule,Position,Trs>> dummyList = new ArrayList<Triple<Rule,Position,Trs>>();
                for(Triple<Rule,Position,Trs> rPtriple : narrowList){
                    dummyList.add(0, rPtriple);
                }
                narrowList = dummyList;
                narrowList.add(new Triple<Rule,Position,Trs>(pair.dp, Position.create(),Trs.P));
            }
            // both cases (forward and backward narrowing) are equal now
            TRSSubstitution actMatcher;
            Position actPos;
            Rule actRule;
            TRSTerm actL;
            TRSTerm actR;
            TRSTerm newTerm;
            TRSFunctionApplication actSubterm;
            // check the whole narrowing list
            for(Triple<Rule,Position,Trs> actPair : narrowList){
                actRule = actPair.x;
                actPos = actPair.y;
                // get subterm where the unification succeeded and check if this is an innermost step
                actSubterm = (TRSFunctionApplication) actTerm.getSubterm(actPos);
                redexList.add(new Pair<TRSFunctionApplication,Trs>(actSubterm,actPair.z));
                // do the narrowing
                Set<TRSVariable> vars = actTerm.getVariables();
                actRule = actRule.renameVariables(vars);
                actL = actRule.getLeft();
                actR = actRule.getRight();
                actMatcher = actL.getMatcher(actSubterm);
                newTerm = actTerm.replaceAt(actPos,actR.applySubstitution(actMatcher));
                actTerm = newTerm;
            }
            return redexList;
        }
    }

    /**
     * Class which represents a pair of terms which stores the way of narrowings
     * you have to use to narrow from <code>pair.x</code> to <code>pair.y</code>
     * .
     *
     * @author Matthias Sondermann
     */
    @SuppressWarnings("serial")
    private class NarrowPair extends Pair<TRSTerm, TRSTerm> {

        private Direction narrowDir;
        private List<Triple<Rule, Position, Trs>> narrowList;
        private Map<Rule, Integer> numOfAppl;

        // only for proof
        private Rule dp;

        /**
         * constructor for a narrowing pair which initializes all attributes to
         * null even pair.x and pair.y
         */
        public NarrowPair() {
            super(null, null);
            this.narrowDir = null;
            this.narrowList = null;
            this.numOfAppl = null;
            this.dp = null;
        }

        /**
         * constructor for a narrowing pair (narrowRule must be non-null). the
         * rRules are used to remember how often a rule is used.
         */
        public NarrowPair(final Rule narrowRule, final Set<Rule> allRules) {
            super(narrowRule.getLeft(), narrowRule.getRight());

            this.narrowDir = Direction.NONE;
            this.narrowList = new ArrayList<Triple<Rule, Position, Trs>>();
            this.numOfAppl = new HashMap<Rule, Integer>();
            this.dp = narrowRule;
            // initialise every rule with 0
            for (final Rule rule : allRules) {
                this.numOfAppl.put(rule, 0);
            }
        }

        /**
         * constructor for a narrowing pair
         */
        public NarrowPair(final TRSTerm lhs, final TRSTerm rhs,
                final NarrowPair parentPair,
                final Triple<Rule, Position, Trs> addedNarrowing,
                final Direction narrowDir) {
            super(lhs, rhs);

            this.narrowList = new ArrayList<Triple<Rule, Position, Trs>>();
            this.numOfAppl = new HashMap<Rule, Integer>();
            this.narrowDir = narrowDir;
            this.dp = parentPair.dp;

            // copy the old narrowings to the new
            for (final Triple<Rule, Position, Trs> triple : parentPair.narrowList) {
                this.narrowList.add(triple);
            }
            // copy the old number of narrowings to the new
            for (final Map.Entry<Rule, Integer> entry : parentPair.numOfAppl
                    .entrySet()) {
                final Rule rule = entry.getKey();
                this.numOfAppl.put(rule, Integer.valueOf(entry.getValue()));
            }
            // add additional narrowing (actually this is the difference between
            // the parentPair and the new pair
            this.narrowList.add(addedNarrowing);
            this.numOfAppl.put(addedNarrowing.x, this
                    .getNrOfAppls(addedNarrowing.x) + 1);
        }

        @Override
        public String toString() {
            return this.x + " ~> " + this.y;
        }

        /**
         * returns the number of applications of <code>rule</code> to the left
         */
        public int getNrOfAppls(final Rule rule) {
            return this.numOfAppl.get(rule);
        }

        /**
         * returns the list of used narrowings
         */
        public List<Triple<Rule, Position, Trs>> getNarrowList() {
            return this.narrowList;
        }

        /**
         * returns a pair containing the left and right term of the narrowing
         * pair
         */
        public Pair<TRSTerm, TRSTerm> getTermPair() {
            return new Pair<TRSTerm, TRSTerm>(this.x, this.y);
        }

        public Direction getDirection() {
            return this.narrowDir;
        }

        public Pair<TRSTerm, TRSTerm> getStandardRepresentation() {
            return new Pair<TRSTerm, TRSTerm>(this.x.getStandardRenumbered(), this.y
                    .getStandardRenumbered());
        }

        /**
         * Returns a new NarrowPair with the same attributes. This is used if a
         * semiunifying pair is found to add the first or the last narrowing.
         */
        public NarrowPair copy() {
            final NarrowPair copy = new NarrowPair();
            copy.x = this.x;
            copy.y = this.y;
            copy.dp = this.dp;
            copy.narrowDir = this.narrowDir;
            copy.narrowList = new ArrayList<Triple<Rule, Position, Trs>>(
                    this.narrowList);
            copy.numOfAppl = new LinkedHashMap<Rule, Integer>(this.numOfAppl);
            return copy;
        }
    }
}
