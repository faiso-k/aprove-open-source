package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * this processor searches for a QDP-Loop using methods from the NonTerminationProcessor
 *      and returns a corresponding Set of TRS-Loops;
 * the main task consists in re-building the CONTEXTS which go lost during the search for a QDP-Loop
 *
 * @author Sebastian Weise
 */
public class QTRSLoopFinder extends QTRSProcessor {

    private static final Logger log = Logger
            .getLogger("aprove.verification.dpframework.DPProblem.Processors.QTRSLoopFinder");

    @ParamsViaArguments({"TotalLimit","LeftLimit","RightLimit"})
    public QTRSLoopFinder(final int totalLimit, final int leftLimit, final int rightLimit) {

        // default-values for the methods copied from NonTerminationProcessor
        this.heuristic = Heuristic.NORMAL;
        this.totalLimit = totalLimit;
        this.rightLimit = rightLimit;
        this.leftLimit = leftLimit;
    }

    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        // TODO check that computed loop is a Q (or innermost) loop and always return true here
        return qtrs.getQ().isEmpty();
    }

    @Override
    protected Result processQTRS(final QTRSProblem qtrs, final Abortion aborter, final RuntimeInformation rti)
            throws AbortionException {
        // get the Dependency Pairs of the QTRSProblem "qtrs"
        final ImmutableTriple<ImmutableSet<Rule>, ImmutableMap<FunctionSymbol, FunctionSymbol>, ImmutableMap<Rule, List<Pair<Position, Rule>>>> dps = qtrs
                .getDPs();
        final ImmutableSet<Rule> dpRules = dps.x;
        final ImmutableMap<FunctionSymbol, FunctionSymbol> defToTup = dps.y;
        final ImmutableMap<Rule, List<Pair<Position, Rule>>> mapRruleToDp = dps.z;

        // we have to map Tuple-Symbols to their original Functions-Symbols, so
        // reverse "defToTup" to "tupToDef"
        final HashMap<FunctionSymbol, FunctionSymbol> tupToDef = new HashMap<FunctionSymbol, FunctionSymbol>();
        final Set<Map.Entry<FunctionSymbol, FunctionSymbol>> defToTupSet = defToTup
                .entrySet();
        for (final Map.Entry<FunctionSymbol, FunctionSymbol> defTup : defToTupSet) {
            tupToDef.put(defTup.getValue(), defTup.getKey());
        }

        // we have to map Dependency Pairs to their original TRS-Rules (+
        // Positions),
        // so reverse "mapRruleToDp" to "mapDpToRrule"
        final HashMap<Rule, HashSet<Pair<Rule, Position>>> mapDpToRrule = this
                .reverse(mapRruleToDp);

        // make a QDPProblem from our QTRSProblem as input for the methods
        // copied from NonTerminationProcessor
        final QDPProblem qdpProblem = QDPProblem.create(dpRules, qtrs, true);

        // now feed the methods copied from NonTerminationProcessor with the
        // QDPProblem
        final NonTerminationProcedure nonTermProc = new NonTerminationProcedure(
                qdpProblem);
        // if "pairMatcherSemiunifier" != Null then
        // a QDP-Loop has been found and 1st Substitution = Matcher and 2nd =
        // Semiunifier
        final Pair<NarrowPair, Pair<TRSSubstitution, TRSSubstitution>> pairMatcherSemiunifier = nonTermProc
                .processQDPProblem(aborter);

        if (pairMatcherSemiunifier != null) {
            // a QDP-Loop has been found ! we now want to build each possible
            // TRS-Loop from it

            final Set<Loop> loops = this.getLoops(pairMatcherSemiunifier.x,
                    pairMatcherSemiunifier.y.y, mapDpToRrule, tupToDef);

            /*
             * add the Matcher for the instance of the first term of a loop in
             * the last term of a loop to each TRS-Loop;
             * this Matcher will be the same for each TRS-Loop
             * (= the Matcher of the corresponding Semi-Unification-Problem)
             */
            final TRSSubstitution matcher = pairMatcherSemiunifier.y.x;
            for (final Loop actLoop : loops) {
                actLoop.setMatcher(matcher);
            }

            // Some sanity checks, really needed?
            for (final Loop actLoop : loops) {
                if (! actLoop.check()) {
                    if (QTRSLoopFinder.log.isLoggable(Level.INFO)) {
                        QTRSLoopFinder.log.info("Loop check failed for " + actLoop);
                    }
                    return ResultFactory.unsuccessful();
                }
            }


            final boolean srsProof = Options.certifier.isRainbow() && Boolean.TRUE.equals(rti.getMetadata(Metadata.IS_SRS));
            return ResultFactory.disproved(new NonTerminationProof(loops, srsProof, qtrs));
        } else {
            // no QDP-Loop has been found, so we can't build any TRS-Loops
            QTRSLoopFinder.log.info("The QDPLoopFinder didn't find a QDP-Loop, so no TRS-Loops can be generated.\n");
            return ResultFactory.unsuccessful();
        }
    }

    // reverse "mapRruleToDp" to "mapDpToRrule"
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

    /**
     * adapted and adjusted from NonTerminationProcessor ("printRewritingSequence")
     */
    private Set<Loop> getLoops(final NarrowPair narrowPair,
            final TRSSubstitution semiUnifier,
            final HashMap<Rule, HashSet<Pair<Rule, Position>>> mapDpToRrule,
            final HashMap<FunctionSymbol, FunctionSymbol> tupToDef) {

        Set<Loop> result = new LinkedHashSet<Loop>();

        final TRSTerm dpLhs = narrowPair.dp.getLeft();

        List<Triple<Rule, Position, Trs>> narrowList = narrowPair
                .getNarrowList();

        // if the dp directly semiunifies nothing is to check
        if (narrowList.isEmpty()) {
            // "The DP semiunifies directly so there is only one rewrite step from "
            // + dpLhs.applySubstitution(semiUnifier) + " to " +
            // dpRhs.applySubstitution(semiUnifier)
            final Loop loop = new Loop();
            loop.getTerms().add(
                    this.replaceLeadingTupleSymbol(dpLhs
                            .applySubstitution(semiUnifier), tupToDef));
            result.addAll(this.branche(loop, mapDpToRrule.get(narrowPair.dp),
                    Position.create()));
            return result;
        }

        final Direction dir = narrowPair.narrowDir;

        // check narrowing direction to know how to narrow
        // forward narrowing: start with rhs of the initial dp and narrow up to
        // pair.y
        if (dir == Direction.RIGHT) {
            final Loop loop = new Loop();
            loop.getTerms().add(
                    this.replaceLeadingTupleSymbol(narrowPair.x
                            .applySubstitution(semiUnifier), tupToDef));
            result.addAll(this.branche(loop, mapDpToRrule.get(narrowPair.dp),
                    Position.create()));
        }
        // backward narrowing: start with pair.x and narrow up to the lhs of the
        // initial dp
        else {
            final Loop loop = new Loop();
            loop.getTerms().add(
                    this.replaceLeadingTupleSymbol(narrowPair.x
                            .applySubstitution(semiUnifier), tupToDef));
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
                    this.add(actLoop, actRule, actPos, Position.create());
                }
            }

            if (actTrs == Trs.P) {
                result = (this.branche(result, mapDpToRrule.get(actRule),
                        Position.create()));
            }
        }

        if (dir == Direction.LEFT) {
            result = (this.branche(result, mapDpToRrule.get(narrowPair.dp),
                    Position.create()));
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
        final Set<Loop> result = new LinkedHashSet<Loop>();

        Loop copy;

        for (final Pair<Rule, Position> redRuleContextStep : redRulesContextSteps) {
            copy = loop.shallowCopy();
            this.add(copy, redRuleContextStep.x, redPos, redRuleContextStep.y);
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
        final Set<Loop> result = new LinkedHashSet<Loop>();

        for (final Loop actLoop : loops) {
            result.addAll(this.branche(actLoop, redRulesContextSteps, redPos));
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

    private class NonTerminationProof extends QTRSProof implements aprove.prooftree.Proofs.HasNonterminatingTerm {

        Set<Loop> loops;
        boolean srs;
        private final QTRSProblem origObl;

        public NonTerminationProof(
                final Set<Loop> loops,
 final boolean srs, final QTRSProblem origObl) {
            this.loops = loops;
            this.srs = srs;
            this.origObl = origObl;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder retStr = new StringBuilder();

            //retStr.append(eu.math("The TRS R consists of the following rules:"
            //        + eu.linebreak()));
            //retStr.append(eu.set(this.qdpProblem.getR(), Export_Util.RULES)
            //        + eu.linebreak());

            retStr.append("The following loops were found:");
            retStr.append(eu.linebreak());
            retStr.append(eu.cond_linebreak());
            for (final Loop actLoop : this.loops) {
                retStr.append(actLoop.export(eu));
                retStr.append(eu.linebreak());
            }
            return retStr.toString();
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            return CPFTag.TRS_NONTERMINATION_PROOF.create(
                doc,
                this.loops.iterator().next().toCPF(doc, xmlMetaData, this.origObl.getR(), null));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return !modus.isPositive();
        }

        @Override
        public TRSTerm getNonterminatingTerm() {
            final Loop loop = this.loops.iterator().next();
            final TRSTerm res = loop.getTerms().get(0);
            return res;
        }

    }

    //*************************************************************************************************
    // Help-Methods and -Attributes copied and adjusted from NonTerminationProcessor to find a QDP-Loop
    //*************************************************************************************************

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
        /**
         * if we have a SRS it suffices to narrow with matching instead of
         * semiunification
         */
        private final boolean matchingSuffices;

        public NonTerminationProcedure(final QDPProblem qdpProblem) {
            this.qdpProblem = qdpProblem;
            this.rRuleMap = qdpProblem.getRwithQ().getRuleMap();
            this.rReverseRuleMap = qdpProblem.getRwithQ().getReverseRuleMap();
            this.actualTotalLimit = QTRSLoopFinder.this.totalLimit;

            // check if it suffices to narrow with matching and not with
            // semiunification
            this.matchingSuffices = this.qdpProblem.getMaxArity() == 1 ? true
                    : false;
        }

        /**
         * Tries to find a narrow pair which semiunifies.
         */
        private Pair<NarrowPair, Pair<TRSSubstitution, TRSSubstitution>> processQDPProblem(
                final Abortion aborter) throws AbortionException {

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

            // if a pair semiunifies this will be the matcher and the
            // semiunifier
            Pair<TRSSubstitution, TRSSubstitution> subst;

            // initial closure step with dependency pairs
            this.rulesFromPtoCheck = new ArrayList<NarrowPair>();
            this.rulesFromPalreadyChecked = new LinkedHashSet<Pair<TRSTerm, TRSTerm>>();
            // first add all needed pRules to the dp sets
            for (final Rule dp : this.pRules) {
                final NarrowPair newPair = new NarrowPair(dp, this.allRules);
                // check dp only if it wasn't already checked earlier
                // (use standard representation to avoid adding two pairs which
                // are equal under variable renaming
                if (!this.rulesFromPalreadyChecked.contains(newPair
                        .getStandardRepresentation())) {
                    // is the pair semiunifiable?
                    subst = this.testPair(newPair, aborter);
                    if (subst != null) {
                        // since a semiunifiable pair is found nontermination is
                        // proved and so nothing more is to do
                        return new Pair<NarrowPair, Pair<TRSSubstitution, TRSSubstitution>>(
                                newPair, subst);
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
            Pair<Direction, Direction> directionOrder;
            switch (QTRSLoopFinder.this.heuristic) {
                case ONLY_FORWARD_NARROWING:
                    directionOrder = new Pair<Direction, Direction>(
                            Direction.RIGHT, Direction.NONE);
                    this.narrowInVars = false;
                    break;
                case NORMAL:
                    // if P united with R is left-linear: first narrow backwards
                    if (this.leftLinear) {
                        directionOrder = new Pair<Direction, Direction>(
                                Direction.LEFT, Direction.RIGHT);
                    }
                    // if P united with R is right-linear: first narrow forwards
                    else if (this.rightLinear) {
                        directionOrder = new Pair<Direction, Direction>(
                                Direction.RIGHT, Direction.LEFT);
                    }
                    // if P united with R is not left-linear and not
                    // right-linear: first narrow backwards and narrow into
                    // variables
                    else {
                        directionOrder = new Pair<Direction, Direction>(
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
            final Pair<Direction, Pair<NarrowPair, Pair<TRSSubstitution, TRSSubstitution>>> returnPair = this
                    .doHeuristic(directionOrder, aborter);
            // if a pair was found that semiunifies nontermination is proved
            if (returnPair.y != null) {
                return new Pair<NarrowPair, Pair<TRSSubstitution, TRSSubstitution>>(
                        returnPair.y.x, returnPair.y.y);
            }
            // no narrowing could show nontermination
            return null;
        }

        /**
         * First do closure procedure into direction <code>dirs.x</code> and
         * then into direction <code>dirs.y</code> if needed.
         */
        private Pair<Direction, Pair<NarrowPair, Pair<TRSSubstitution, TRSSubstitution>>> doHeuristic(
                final Pair<Direction, Direction> dirs, final Abortion aborter)
                throws AbortionException {
            Pair<NarrowPair, Pair<TRSSubstitution, TRSSubstitution>> dummyPair = null;

            // narrow to the first direction
            dummyPair = this.doClosure(dirs.x, aborter);
            if (dummyPair != null) {
                return new Pair<Direction, Pair<NarrowPair, Pair<TRSSubstitution, TRSSubstitution>>>(
                        dirs.x, dummyPair);
            }
            // since the narrowing to the first direction took place the total
            // limit has to be updated
            if (dirs.x == Direction.LEFT) {
                this.actualTotalLimit -= QTRSLoopFinder.this.leftLimit;
            } else {
                this.actualTotalLimit -= QTRSLoopFinder.this.rightLimit;
            }
            if (this.actualTotalLimit <= 0 || dirs.y == Direction.NONE) {
                // nothing more to do and dummyPair is null
                return new Pair<Direction, Pair<NarrowPair, Pair<TRSSubstitution, TRSSubstitution>>>(
                        dirs.y, dummyPair);
            }
            // if narrowing to the first direction failed now narrow to the
            // second direction
            dummyPair = this.doClosure(dirs.y, aborter);
            return new Pair<Direction, Pair<NarrowPair, Pair<TRSSubstitution, TRSSubstitution>>>(
                    dirs.y, dummyPair);
        }

        /**
         * Do narrowings in direction <code>actDir</code> until a pair which
         * semiunifies is found or the limit is reached.
         */
        private Pair<NarrowPair, Pair<TRSSubstitution, TRSSubstitution>> doClosure(
                final Direction actDir, final Abortion aborter)
                throws AbortionException {

            // set the actual limit depending on the direction
            int actLimit;
            if (actDir == Direction.RIGHT) {
                actLimit = QTRSLoopFinder.this.rightLimit;
            } else {
                actLimit = QTRSLoopFinder.this.leftLimit;
            }

            // some needed stuff
            final List<NarrowPair> closure = new ArrayList<NarrowPair>();
            closure.addAll(this.rulesFromPtoCheck);
            final Set<Pair<TRSTerm, TRSTerm>> done = new LinkedHashSet<Pair<TRSTerm, TRSTerm>>();
            done.addAll(this.rulesFromPalreadyChecked);
            Pair<TRSSubstitution, TRSSubstitution> subst = null;

            // do more closure steps as long as new narrow-pairs result out of
            // narrowing.
            // take every element which was added to and never removed from
            // closure list
            while (!closure.isEmpty()) {
                aborter.checkAbortion();
                // get a custom narrow pair (take wlog the first one)
                final NarrowPair actPair = closure.get(0);
                final List<NarrowPair> newNarrowedPairs = new ArrayList<NarrowPair>();
                // try to narrow pair with every rule and get all new narrow
                // pairs
                final Set<NarrowPair> actNarrowedPairs = this
                        .doOneNarrowingStep(actPair, actDir, actLimit, aborter);
                // add all new narrow pairs which have not been computed yet
                for (final NarrowPair actNewPair : actNarrowedPairs) {
                    // check this pair only if it or a pair that is equal to
                    // this except by variable renaming was never checked before
                    if (!done.contains(actNewPair.getStandardRepresentation())) {
                        // is the new pair semiunifiable?
                        subst = this.testPair(actNewPair, aborter);
                        if (subst != null) {
                            // nontermination proved so nothing more is to do
                            return new Pair<NarrowPair, Pair<TRSSubstitution, TRSSubstitution>>(
                                    actNewPair, subst);
                        }
                        // this pair has to be narrowed later
                        newNarrowedPairs.add(actNewPair);
                        // never add this pair again
                        done.add(actNewPair.getStandardRepresentation());
                    }
                }
                // add all new narrow pairs to the closure list
                closure.addAll(newNarrowedPairs);
                // actPair will never be touched again
                closure.remove(actPair);
            }
            // closure list is empty and no semiunification succeded
            // so nontermination could not be proved with this applLimit
            return null;
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
            return subst;
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
