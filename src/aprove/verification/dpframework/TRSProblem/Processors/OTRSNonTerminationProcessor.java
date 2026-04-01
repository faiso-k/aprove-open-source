package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Utility.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * this Processor searchs for an Outermost-Loop in an OTRSPRoblem;
 * the Methods for finding and checking an Outermost-Loop are PUBLIC;
 * this code can be modified easily to
 *      use the Method "getOutermostLoop(...)" for finding an Outermost-Loop several times and
 *          always continue the search from the last point of state;
 *          see corresponding comments on this method below;
 *
 * ! note the an OTRSProblem contains GENERALIZED Rules where new Variables on the Rhs's may occur;
 * as our so-far LoopFinder only works for SIMPLE Rules,
 *      there is a method "simplify" to reduce this case to the case of only Simple Rules;
 *          the approach used so far is correct, but not complete;
 *          I've tried to consider possible extentions of this approach in the implementation;
 *
 * @author Sebastian Weise
 */

@NoParams
public class OTRSNonTerminationProcessor extends OTRSProcessor {

    private static final Logger log = Logger
            .getLogger("aprove.verification.dpframework.DPProblem.Processors.OTRSNonTerminationProcessor");

    @Override
    public boolean isOTRSApplicable(final OTRSProblem R) {
        return true;
    }

    @Override
    protected Result processOTRS(final OTRSProblem R, final Abortion aborter, final RuntimeInformation rti)
            throws AbortionException {

        // as our so-far LoopFinder only works for SIMPLE Rules,
        //      we first generate a SIMPLE TRS from the Generalized TRS R

        ImmutableSet<Rule> simpleRules;

        final Pair<ImmutableSet<Rule>, Map<Rule, GeneralizedRule>> tempPair = this
                .simplify(R.getR());
        simpleRules = tempPair.x;

        // this information will be needed to rebuild our GeneralizedLoop correctly
        final Map<Rule, GeneralizedRule> rulesToGeneralizedRules = tempPair.y;

        // search for an Outermost-Loop
        final Loop loop = this.getOutermostLoop(simpleRules, aborter);

        if (loop != null) {
            // we found an Outermost-Loop !
            return ResultFactory.disproved(new OutermostNonTerminationProof(R, this.generalize(loop,
                    rulesToGeneralizedRules)));
        } else {
            // we didn't find an Outermost-Loop
            OTRSNonTerminationProcessor.log.info("No Loop or no Outermost-Loop found.\n");

            return ResultFactory.unsuccessful();
        }
    }

    /**
     * this method generates a SIMPLE TRS from our Generalized OTRSProblem and
     *      provides further information to rebuild our Generalized Loop correctly
     */
    private Pair<ImmutableSet<Rule>, Map<Rule, GeneralizedRule>> simplify(
            final ImmutableSet<? extends GeneralizedRule> generalizedRules) {

        // if the OTRS contains "real" GeneralizedRules, we transform them into Simple Rules
        //      by replacing unbound Variables on the Rhs by the Lhs;
        // this easy method is correct, but of course not complete;
        // note that for the Outermost-Test we only need the LEFT Rule-Sides !

        final Set<Rule> simpleRules = new LinkedHashSet<Rule>();

        // this information will be needed to rebuild our Generalized Loop correctly;
        //      a Map from each "simplified" new Simple Rule to it's original Generalized Rule
        final Map<Rule, GeneralizedRule> rulesToGeneralizedRules = new LinkedHashMap<Rule, GeneralizedRule>();

        TRSFunctionApplication actLhs;
        TRSTerm actRhs, actSubTerm, newRhs;
        Set<TRSVariable> actUnboundVariables;
        Collection<Pair<Position, TRSTerm>> actPositionsAndSubTerms;
        Position actPos;
        Rule newRule;

        for (final GeneralizedRule actGeneralizedRule : generalizedRules) {
            if (actGeneralizedRule instanceof Rule) {
                simpleRules.add((Rule) actGeneralizedRule);
            } else {
                actLhs = actGeneralizedRule.getLeft();
                actRhs = actGeneralizedRule.getRight();
                actUnboundVariables = actGeneralizedRule
                        .getUnboundedVariables();
                actPositionsAndSubTerms = actRhs.getPositionsWithSubTerms();

                newRhs = actRhs;

                for (final Pair<Position, TRSTerm> actPosTerm : actPositionsAndSubTerms) {
                    actPos = actPosTerm.x;
                    actSubTerm = actPosTerm.y;

                    if (actUnboundVariables.contains(actSubTerm)) {
                        newRhs = newRhs.replaceAt(actPos, actLhs);
                    }
                }

                newRule = Rule.create(actLhs, newRhs);

                simpleRules.add(newRule);

                rulesToGeneralizedRules.put(newRule, actGeneralizedRule);
            }
        }

        return new Pair<ImmutableSet<Rule>, Map<Rule, GeneralizedRule>>(
                ImmutableCreator.create(simpleRules), rulesToGeneralizedRules);
    }

    /**
     * this method rebuilds our Generalized Loop from a Simple Loop that we have found and
     *      from our corresponding additional information
     */
    private GeneralizedLoop generalize(final Loop simpleLoop,
            final Map<Rule, GeneralizedRule> rulesToGeneralizedRules) {

        final ArrayList<Rule> simpleRules = simpleLoop.getRules();
        final ArrayList<TRSSubstitution> simpleSubstitutions = simpleLoop
                .getSubstitutions();

        final ArrayList<GeneralizedRule> newRules = new ArrayList<GeneralizedRule>();
        final ArrayList<TRSSubstitution> newSubstitutions = new ArrayList<TRSSubstitution>();

        Rule actSimpleRule;
        TRSSubstitution actSimpleSubstitution, matcherLhs, matcherRhs, matcherRule, newSubstitution;
        GeneralizedRule actGeneralizedRule, newGeneralizedRule;
        final Set<TRSVariable> variablesToAvoid = new HashSet<TRSVariable>();
        TRSFunctionApplication newGeneralizedLhs;
        TRSTerm newGeneralizedRhs;

        for (int i = 0; i <= simpleRules.size() - 1; i++) {
            actSimpleRule = simpleRules.get(i);
            actSimpleSubstitution = simpleSubstitutions.get(i);

            actGeneralizedRule = rulesToGeneralizedRules.get(actSimpleRule);

            if (actGeneralizedRule == null) {
                // "actSimpleRule" was also originally a Simple Rule, so we just add it
                newRules.add(actSimpleRule);
                newSubstitutions.add(actSimpleSubstitution);
            } else {

                // "actSimpleRule" may have been Variable-renamed in comparison to
                //      it's equivalent in "rulesToGeneralizedRules" and so in comparison to
                //      it's original Generalized Rule "actGeneralizedRule", too !
                // we have to consider this while rebuilding our Generalized Loop !

                // first we Variable-rename the original Generalized Rule "actGeneralizedRule" completely

                variablesToAvoid.clear();
                variablesToAvoid.addAll(actSimpleRule.getVariables());
                variablesToAvoid.addAll(actSimpleSubstitution.getDomain());
                variablesToAvoid.addAll(actSimpleSubstitution
                        .getVariablesInCodomain());

                final aprove.verification.dpframework.BasicStructures.Utility.FreshVarGenerator gen = new aprove.verification.dpframework.BasicStructures.Utility.FreshVarGenerator(
                        variablesToAvoid);

                newGeneralizedLhs = actGeneralizedRule.getLeft()
                        .renameVariables(gen);
                newGeneralizedRhs = actGeneralizedRule.getRight()
                        .renameVariables(gen);

                newGeneralizedRule = GeneralizedRule.create(newGeneralizedLhs,
                        newGeneralizedRhs);

                newRules.add(newGeneralizedRule);

                // then we match the new Variable-renamed original Generalized Rule to "actSimpleRule"
                //      and get the Matcher "matcherRule"

                matcherLhs = newGeneralizedLhs.getMatcher(actSimpleRule
                        .getLeft());
                matcherRhs = newGeneralizedRhs.getMatcher(actSimpleRule
                        .getRight());
                matcherRule = matcherLhs.extend(matcherRhs);

                // we have to compose "matcherRule" and "actSimpleSubstitution" to get our
                //      new correct "generalized Substitution"

                newSubstitution = matcherRule.compose(actSimpleSubstitution);

                newSubstitution = newSubstitution.restrictTo(newGeneralizedRule
                        .getVariables());

                newSubstitutions.add(newSubstitution);
            }
        }

        return new GeneralizedLoop(simpleLoop.getTerms(), newRules, simpleLoop
                .getPositions(), newSubstitutions, simpleLoop.getPosition(),
                simpleLoop.getMatcher());
    }

    /**
     * returns "null" if no Outermost-Loop is found;
     * always returns the same result;
     * but the code can be modified easily to use the method several times
     *      and always continue the search from the last point of state
     *      by declaring the "LoopFinder"-Object as a global Variable
     *      as "LoopFinder" keeps track of the search for a TRS-Loop
     */
    public Loop getOutermostLoop(final ImmutableSet<Rule> R,
            final Abortion aborter) throws AbortionException {
        final LoopFinder loopFinder = new LoopFinder(R,
                LoopFinder.Heuristic.NORMAL, 3, 3, 3);
        Set<Loop> loops = null;
        Loop loop = null;

        final PLAIN_Util eu = new PLAIN_Util();

        label: do {
            loops = loopFinder.getLoops(aborter);

            if (loops == null) {
                // the LoopFinder won't find any more Loops or a Loop-Check-Error has occured
                OTRSNonTerminationProcessor.log
                        .info("No or no more Loops found (or a Loop-Check-Error has occured).\n");
                break label;
            } else {
                // we have found some Loops; now let's check if there is an Outermost-Loop among them
                OTRSNonTerminationProcessor.log.info("The LoopFinder has found one or more Loops.\n\n");
                for (final Loop actLoop : loops) {
                    OTRSNonTerminationProcessor.log.info("Now looking at:\n\n" + actLoop.export(eu) + "\n");

                    if (this.isOutermostLoop(actLoop, R)) {
                        OTRSNonTerminationProcessor.log.info("Outermost-Loop found!\n");

                        loop = actLoop;

                        break label;
                    }

                    OTRSNonTerminationProcessor.log.info("No Outermost-Loop.\n\n");
                }

                OTRSNonTerminationProcessor.log.info("No Outermost-Loop among the found Loops.\n");
            }
        } while (true);

        return loop;
    }

    /**
     * checks if a Loop is an Outermost-Loop
     *      (respecting any contexts occuring during the infinite iteration!)
     */
    public boolean isOutermostLoop(final Loop loop,
            final ImmutableSet<Rule> rules) {
        final ArrayList<TRSTerm> terms = loop.getTerms();
        final ArrayList<Position> positions = loop.getPositions();

        final Context C = loop.getContext();
        final Position p = C.getPosition();

        final TRSSubstitution my = loop.getMatcher();

        final ExtendedMatchingAndIdentityProblemSolver extendedMatchingAndIdentityProblemSolver = new ExtendedMatchingAndIdentityProblemSolver(
                my);

        final Set<Pair<TRSTerm, TRSTerm>> M = new LinkedHashSet<Pair<TRSTerm, TRSTerm>>();
        TRSTerm l;

        for (int i = 0; i <= positions.size() - 1; i++) {
            final TRSTerm t = terms.get(i);
            final Position q = positions.get(i);

            for (final Rule actRule : rules) {
                l = actRule.getLeft();

                // build and check non-extended Matching-Problems
                for (final Position pApostroph : q.getTruePrefixes()) {
                    M.clear();
                    M.add(new Pair<TRSTerm, TRSTerm>(t.getSubterm(pApostroph), l));

                    if (extendedMatchingAndIdentityProblemSolver
                            .solveMatchingProblem(M)) {
                        return false;
                    }
                }

                // build and check extended Matching-Problems
                for (final Position pApostroph : p.getTruePrefixes()) {
                    M.clear();

                    if (extendedMatchingAndIdentityProblemSolver
                            .solveExtendedMatchingProblem(C
                                    .getSubcontext(pApostroph), l, C
                                    .applySubstitution(my), t
                                    .applySubstitution(my), M)) {
                        return false;
                    }
                }
            }
        }

        return true;
    }

    private class OutermostNonTerminationProof extends QTRSProof {

        private final OTRSProblem R;
        private final GeneralizedLoop loop;

        public OutermostNonTerminationProof(final OTRSProblem R,
                final GeneralizedLoop loop) {
            this.R = R;
            this.loop = loop;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder retStr = new StringBuilder();

            retStr.append(this.R.export(eu) + eu.linebreak());

            retStr.append(this.loop.export(eu));

            retStr.append(eu.linebreak() + "We used "
                + eu.cite(Citation.THIEMANN_LOOPS_UNDER_STRATEGIES)
                + " to show that this Loop is an Outermost-Loop.");

            return retStr.toString();
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            return CPFTag.TRS_NONTERMINATION_PROOF.create(doc, this.loop.toCPF(doc, xmlMetaData, this.R.getR()));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return !modus.isPositive();
        }

    }
}
