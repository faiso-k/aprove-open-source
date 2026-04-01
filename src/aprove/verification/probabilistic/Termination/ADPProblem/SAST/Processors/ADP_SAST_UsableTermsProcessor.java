package aprove.verification.probabilistic.Termination.ADPProblem.SAST.Processors;

import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.*;
import aprove.verification.probabilistic.Termination.ADPProblem.SAST.*;

/**
 * Usable Terms Processor as described in Leon's master's thesis
 * (Analyzing Strong Almost-Sure Termination for Probabilistic Term Rewriting Using Dependency Pairs, 2025)
 *
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public class ADP_SAST_UsableTermsProcessor extends ADP_SAST_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isSAST_ADPApplicable(final ADP_SAST_Problem qdp) {
        // Only applies if we restrict to innermost evaluation and basic start terms
        if (!qdp.getInnermost() || !qdp.isBasic()) {
            return false;
        }
        final ProbQComplexityDependencyGraph graph = qdp.getDependencyGraph();
        return graph.doUnusablePairsExist();
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processSAST_ADPProblem(final ADP_SAST_Problem qdp, final Abortion aborter) throws AbortionException {
        final Set<TRSFunctionApplication> unusableTermsSet = new HashSet<>();

        final ProbQComplexityDependencyGraph graph = qdp.getDependencyGraph();

        final Set<ProbabilisticRule> p_adps = qdp.getP();
        final Set<ProbabilisticRule> s_adps = qdp.getS();
        final Set<ProbabilisticRule> k_adps = qdp.getK();

        final Set<ProbabilisticRule> ReachADPs = qdp.getReach();
        final ProbQComplexityDependencyGraph reachGraph = qdp.getReachDependencyGraph();
        qdp.getSWithQ();
        qdp.getQ();

        // For each P,S,K loop through all DPs and all rhs terms and check if they are usable
        // Starting with P:
        final Set<ProbabilisticRule> newP = new HashSet<>();
        for (final ProbabilisticRule depTuple : p_adps) {
            //Create new rhs
            final HashMultiSet<Pair<TRSTerm, BigFraction>> probabilityMap = new HashMultiSet<>();
            for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : depTuple.getRight().getProbabilityMapping().entrySet()) {
                final TRSTerm term = entry.getKey().getKey();
                final BigFraction prob = entry.getKey().getValue();
                final Integer amount = entry.getValue();

                //Create the term
                final Set<Position> positionsToRemoveAnnos = new HashSet<>();
                for (final Pair<TRSFunctionApplication, Position> termPositionPair : term.getAnnoSubtermsWithPositions(qdp.getDeAnnoMap())) {
                    if (graph.isUnusableTerm(termPositionPair.x)) {
                        positionsToRemoveAnnos.add(termPositionPair.y);
                        unusableTermsSet.add(termPositionPair.x);
                    }
                }
                final TRSTerm newTerm = term.renameAtAllMap(positionsToRemoveAnnos, qdp.getDeAnnoMap());

                probabilityMap.add(new Pair<>(newTerm, prob), amount);
            }
            final MultiDistribution<TRSTerm> rhs = MultiDistribution.create(probabilityMap);
            final ProbabilisticRule newDepTuple = ProbabilisticRule.create(depTuple.getLeft(), rhs);

            newP.add(newDepTuple);
        }

        // Continue with S:
        final Set<ProbabilisticRule> newS = new HashSet<>();
        for (final ProbabilisticRule depTuple : s_adps) {
            //Create new rhs
            final HashMultiSet<Pair<TRSTerm, BigFraction>> probabilityMap = new HashMultiSet<>();
            for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : depTuple.getRight().getProbabilityMapping().entrySet()) {
                final TRSTerm term = entry.getKey().getKey();
                final BigFraction prob = entry.getKey().getValue();
                final Integer amount = entry.getValue();

                //Create the term
                final Set<Position> positionsToRemoveAnnos = new HashSet<>();
                for (final Pair<TRSFunctionApplication, Position> termPositionPair : term.getAnnoSubtermsWithPositions(qdp.getDeAnnoMap())) {
                    if (graph.isUnusableTerm(termPositionPair.x)) {
                        positionsToRemoveAnnos.add(termPositionPair.y);
                        unusableTermsSet.add(termPositionPair.x);
                    }
                }
                final TRSTerm newTerm = term.renameAtAllMap(positionsToRemoveAnnos, qdp.getDeAnnoMap());

                probabilityMap.add(new Pair<>(newTerm, prob), amount);
            }
            final MultiDistribution<TRSTerm> rhs = MultiDistribution.create(probabilityMap);
            final ProbabilisticRule newDepTuple = ProbabilisticRule.create(depTuple.getLeft(), rhs);

            newS.add(newDepTuple);
        }

        // Finish with K:
        final Set<ProbabilisticRule> newK = new HashSet<>();
        for (final ProbabilisticRule depTuple : k_adps) {
            //Create new rhs
            final HashMultiSet<Pair<TRSTerm, BigFraction>> probabilityMap = new HashMultiSet<>();
            for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : depTuple.getRight().getProbabilityMapping().entrySet()) {
                final TRSTerm term = entry.getKey().getKey();
                final BigFraction prob = entry.getKey().getValue();
                final Integer amount = entry.getValue();

                //Create the term
                final Set<Position> positionsToRemoveAnnos = new HashSet<>();
                for (final Pair<TRSFunctionApplication, Position> termPositionPair : term.getAnnoSubtermsWithPositions(qdp.getDeAnnoMap())) {
                    if (graph.isUnusableTerm(termPositionPair.x)) {
                        positionsToRemoveAnnos.add(termPositionPair.y);
                        unusableTermsSet.add(termPositionPair.x);
                    }
                }
                final TRSTerm newTerm = term.renameAtAllMap(positionsToRemoveAnnos, qdp.getDeAnnoMap());

                probabilityMap.add(new Pair<>(newTerm, prob), amount);
            }
            final MultiDistribution<TRSTerm> rhs = MultiDistribution.create(probabilityMap);
            final ProbabilisticRule newDepTuple = ProbabilisticRule.create(depTuple.getLeft(), rhs);

            newK.add(newDepTuple);
        }

        // IGNORE FOR NOW, reachable:
        final Set<ProbabilisticRule> newReach = new HashSet<>();
        for (final ProbabilisticRule depTuple : ReachADPs) {
            // Create new rhs
            final HashMultiSet<Pair<TRSTerm, BigFraction>> probabilityMap = new HashMultiSet<>();
            for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : depTuple.getRight().getProbabilityMapping().entrySet()) {
                final TRSTerm term = entry.getKey().getKey();
                final BigFraction prob = entry.getKey().getValue();
                final Integer amount = entry.getValue();

                // Create the term
                final Set<Position> positionsToRemoveAnnos = new HashSet<>();
                for (final Pair<TRSFunctionApplication, Position> termPositionPair : term.getAnnoSubtermsWithPositions(qdp.getDeAnnoMap())) {
                    if (reachGraph.isUnusableTerm(termPositionPair.x)) {
                        positionsToRemoveAnnos.add(termPositionPair.y);
                        unusableTermsSet.add(termPositionPair.x);
                    }
                }
                final TRSTerm newTerm = term.renameAtAllMap(positionsToRemoveAnnos, qdp.getDeAnnoMap());

                probabilityMap.add(new Pair<>(newTerm, prob), amount);
            }
            final MultiDistribution<TRSTerm> rhs = MultiDistribution.create(probabilityMap);
            final ProbabilisticRule newDepTuple = ProbabilisticRule.create(depTuple.getLeft(), rhs);

            newReach.add(newDepTuple);
        }

        // ensure that annotations of non usable terms are also removed in S and K
        final ADP_SAST_Problem newProblem =
            ADP_SAST_Problem.create(newP, newS, newK, qdp.getSwithQ(), qdp.getReachPQTRS(), qdp.getStrat(), qdp.isBasic(), qdp.getBiAnnoMap());

        final SAST_ADPUsableTermsProof UPPproof = new SAST_ADPUsableTermsProof(qdp, unusableTermsSet);

        final Result result = ResultFactory.proved(newProblem, YNMImplication.EQUIVALENT, UPPproof);
        return result;
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class SAST_ADPUsableTermsProof extends ADP_SAST_Proof {

        private final ADP_SAST_Problem origPQDP;
        private final Set<TRSFunctionApplication> unusableTermsSet;

        private SAST_ADPUsableTermsProof(final ADP_SAST_Problem origObl,
            final Set<TRSFunctionApplication> unusableTermsSet) {
            this.origPQDP = origObl;
            this.unusableTermsSet = unusableTermsSet;
        }

        private static final Citation[] citations = new Citation[] { Citation.LPAR04,
            Citation.FROCOS05,
            Citation.EDGSTAR };

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            res.append(o.paragraph());
            if (this.origPQDP.getInnermost()) {
                res.append("We use the usable terms processor ").append("(Leon's master's thesis)").append(".");
            } else { //full SAST
                res.append("We use the usable terms processor ").append(" (!PROTOTYPE!) ").append(".");
            }
            res.append(o.linebreak());
            res.append("The approximation of the Dependency Graph ")
                .append(o.cite(SAST_ADPUsableTermsProof.citations))
                .append(" gives us the following unusable Terms: ");
            res.append(o.linebreak());
            res.append(o.linebreak());
            res.append(o.set(this.unusableTermsSet, Export_Util.NICE_SET));
            res.append(o.linebreak());
            res.append(o.linebreak());
            res.append("Hence, we can remove the annotations from these terms from every RHS of every ADP in P,S,K.");
            res.append(o.linebreak());

            return o.export(res.toString());
        }
    }
}
