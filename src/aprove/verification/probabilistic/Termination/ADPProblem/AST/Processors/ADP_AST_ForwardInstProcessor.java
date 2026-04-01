package aprove.verification.probabilistic.Termination.ADPProblem.AST.Processors;

import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.AST.*;
import aprove.verification.probabilistic.Termination.ADPProblem.AST.Processors.ADP_AST_InstProcessor.*;

/**
 * The forward instantiation processor for ADPs as described in journal paper of FLOPS24
 *
 * @author J-C Kassing
 */
public class ADP_AST_ForwardInstProcessor extends ADP_AST_TransformationProcessor {

    @ParamsViaArgumentObject
    public ADP_AST_ForwardInstProcessor(final ADP_AST_TransformationProcessor.Arguments arguments) {
        super(ADP_AST_Transformation.ForwardInstantiation, arguments);
    }

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isAST_ADPApplicable(final ADP_AST_Problem qdp) {
        if (qdp.isInnermost()) { /**INNERMOST**/
            return super.isAST_ADPApplicable(qdp);
        } else if (this.initialADPs) { /**BASIC**/
            return super.isAST_ADPApplicable(qdp) && !qdp.getReachPQTRS().isCollapsing();
        } else { /**FULL**/
            return super.isAST_ADPApplicable(qdp) && !qdp.getSwithQ().isCollapsing();
        }
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected
        AbortableIterator<Quintuple<AST_TransformationHeuristic, YNMImplication, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Triple<Position, Set<ProbabilisticRule>, ProbabilisticRule>>>
        getTransformedRules(final Node<ProbabilisticRule> origNode,
            final Graph<ProbabilisticRule, ?> gr,
            final ADP_AST_Problem qdp,
            final Abortion aborter) throws AbortionException {
        return new ADP_AST_TransformationProcessor.MaybeOneIterator<>(
            getTransformed(origNode,
                gr,
                qdp));

    }

    private
        Quintuple<AST_TransformationHeuristic, YNMImplication, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Triple<Position, Set<ProbabilisticRule>, ProbabilisticRule>>
        getTransformed(final Node<ProbabilisticRule> origNode,
            final Graph<ProbabilisticRule, ?> gr,
            final ADP_AST_Problem posQDT) throws AbortionException {
        final Set<ProbabilisticRule> newDTs = new LinkedHashSet<>();
        final Set<Pair<ProbabilisticRule, ProbabilisticRule>> resDTs = new LinkedHashSet<>();
        final Set<Pair<ProbabilisticRule, ProbabilisticRule>> resRules = new LinkedHashSet<>();
        final TRSFunctionApplication ellSharp = origNode.getObject().getLhsInStandardRepresentation();
        final MultiDistribution<TRSTerm> distRHS = origNode.getObject().getRhsInStandardRepresentation();

        for (final Node<ProbabilisticRule> u_to_v : gr.getOut(origNode)) {

            final Set<TRSSubstitution> allMGUs;
            if (this.initialADPs) { /**BASIC**/
                allMGUs = posQDT.getReachDependencyGraph()
                    .getConnectingStarSubstitutions(origNode, u_to_v);
            } else { /**ALL**/
                allMGUs = posQDT.getDependencyGraph()
                    .getConnectingStarSubstitutions(origNode, u_to_v);
            }

            for (final TRSSubstitution mgu : allMGUs) {
                if (Globals.useAssertions) {
                    // Added by cotto, Term.applySubstitution does not want
                    // sigma==null
                    assert (mgu != null) : "Offending nodes where no connecting substitution was found:\nFrom: "
                        + u_to_v
                        + "\nTo: "
                        + origNode
                        + "\nAST_ADP Problem:\n\n"
                        + posQDT.toString();
                }

                //Generate new lhs
                final TRSFunctionApplication ellSharpSigma = ellSharp.applySubstitution(mgu);

                //Generate new Dist rhs for both DT and the new rule
                final HashMultiSet<Pair<TRSTerm, BigFraction>> resProbabilityMapForADP =
                    new HashMultiSet<>();
                final HashMultiSet<Pair<TRSTerm, BigFraction>> resProbabilityMapForRule = new HashMultiSet<>();
                for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : distRHS.getProbabilityMapping().entrySet()) {
                    final TRSTerm term = entry.getKey().getKey();
                    final BigFraction prob = entry.getKey().getValue();
                    final Integer amount = entry.getValue();

                    // Create termSigma
                    final TRSTerm termSigma = term.applySubstitution(mgu);

                    resProbabilityMapForADP.add(new Pair<>(termSigma, prob), amount);
                    resProbabilityMapForRule.add(new Pair<>(termSigma, prob), amount);
                }
                final MultiDistribution<TRSTerm> distSigma = new MultiDistribution<>(resProbabilityMapForADP);

                final ProbabilisticRule generatedDT = ProbabilisticRule.create(ellSharpSigma, distSigma);
                final ProbabilisticRule newDT = posQDT.getDT(generatedDT);
                newDTs.add(newDT);
                resDTs.add(new Pair<>(generatedDT, newDT));

                final ProbabilisticRule generatedRule = generatedDT.removeAnnos(posQDT.getDeAnnoMap());
                final ProbabilisticRule newRule = posQDT.getRule(generatedRule);
                resRules.add(new Pair<>(generatedRule, newRule));
            }
        }

        if (newDTs.contains(origNode.getObject())) {
            // we have the original DT again, hence ignore this transformation
            return null;
        }

        final AST_TransformationHeuristic heuristic = new InstantiationVariableHeuristic(ellSharp, newDTs);

        return new Quintuple<>(heuristic, YNMImplication.EQUIVALENT, resDTs, resRules, null);
    }

}
