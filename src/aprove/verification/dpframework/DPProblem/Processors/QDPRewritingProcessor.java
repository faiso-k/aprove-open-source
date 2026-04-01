/*
 * Created on 16.04.2005
 */
package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * The standard rewriting processor as described in JAR05.
 *
 * Its application is as follows: We require that the usable rule
 * processor was used before and that the d-graph processor was used before!
 *
 * @author thiemann
 */
public class QDPRewritingProcessor extends QDPTransformationProcessor {

    private final boolean beComplete;

    @ParamsViaArgumentObject
    public QDPRewritingProcessor(final Arguments arguments) {
        super(QDPTransformation.Rewriting, arguments);
        this.beComplete = arguments.beComplete;
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        // demand graph-reduces, innermost, and R = U(P,R)
        if (super.isQDPApplicable(qdp) && qdp.QsupersetOfLhsR()) {
            final int n = qdp.getUsableRules().size();
            return n > 0 && n == qdp.getR().size();
        }

        return false;
    }

    @Override
    protected AbortableIterator<Quadruple<TransformationHeuristic, YNMImplication, Set<Pair<Rule, Rule>>, Triple<Position, Set<Rule>, Rule>>> getTransformedRules(final Node<Rule> s_to_t,
        final Graph<Rule, ?> gr,
        final QDPProblem qdp,
        final Abortion aborter) throws AbortionException {
        return new QDPTransformationProcessor.MaybeOneIterator<Quadruple<TransformationHeuristic, YNMImplication, Set<Pair<Rule, Rule>>, Triple<Position, Set<Rule>, Rule>>>(
            this.getTransformed(s_to_t, gr, qdp, aborter));
    }

    private Quadruple<TransformationHeuristic, YNMImplication, Set<Pair<Rule, Rule>>, Triple<Position, Set<Rule>, Rule>> getTransformed(final Node<Rule> s_to_t,
        final Graph<Rule, ?> gr,
        final QDPProblem qdp,
        final Abortion aborter) throws AbortionException {
        final QTRSProblem qtrs = qdp.getRwithQ();
        final QUsableRules usableRules = qdp.getQUsableRulesCalculator();
        final boolean nonOverlapping = qtrs.getCriticalPairs().isNonOverlapping(aborter);
        final boolean confluent = nonOverlapping || qtrs.getCriticalPairs().isInnermostConfluent(aborter);


        // determine redexes // perhaps cache these results

        final Map<FunctionSymbol, ImmutableSet<Rule>> ruleMap = qtrs.getRuleMap();

        final Rule sToT = s_to_t.getObject();
        final TRSFunctionApplication s = sToT.getLeft();
        final TRSTerm t = sToT.getRight();
        subterms : for (final Pair<Position, TRSTerm> posWithSub : t.getPositionsWithSubTerms()) {

            final TRSTerm subTerm = posWithSub.y;
            if (!subTerm.isVariable()) {
                final TRSFunctionApplication sub = (TRSFunctionApplication) subTerm;
                final Set<Rule> possibleRules = ruleMap.get(sub.getRootSymbol());
                if (possibleRules != null) {
                    for (final Rule rule : possibleRules) {
                        final TRSSubstitution matcher = rule.getLeft().getMatcher(subTerm);
                        if (matcher != null) {
                            // okay, we can rewrite
                            final Set<Rule> localUsableRules = usableRules.getUsableRules(Rule.create(s, subTerm));
                            // let us check non-overlappingness
                            if (nonOverlapping) {
                                // there is nothing to do in this case
                            } else {

                                if (confluent) {
                                    // okay, we get confluence for free
                                } else {
                                    // check confluence of usable rules by demanding that root crit pairs are trivial
                                    final AbortableIterator<ImmutableTriple<TRSTerm, TRSTerm, Boolean>> critPairIterator =
                                        GeneralizedRule.getCriticalPairs(localUsableRules);
                                    while (critPairIterator.hasNext(aborter)) {
                                        final ImmutableTriple<TRSTerm, TRSTerm, Boolean> critPair = critPairIterator.next(aborter);
                                        if (critPair.z && !critPair.x.equals(critPair.y)) {
                                            // critical root-overlap
                                            continue subterms; // thus, we cannot ensure confluence
                                        }
                                    }
                                }

                                // now we have to check that l -> r does only have trivial critical pairs with usable rules
                                final Rule l_to_r = rule.getWithRenumberedVariables(TRSTerm.SECOND_STANDARD_PREFIX);
                                final TRSTerm r = l_to_r.getRight();
                                final TRSFunctionApplication l = l_to_r.getLeft();
                                for (final TRSFunctionApplication subl : l.getNonVariableSubTerms()) {
                                    final FunctionSymbol f = subl.getRootSymbol();
                                    for (final Rule usable : localUsableRules) {
                                        if (usable.getRootSymbol().equals(f)) {
                                            final Unification u = new Unification(subl, usable.getLhsInStandardRepresentation());
                                            if (u.unify()) {
                                                // we have detected an overlap
                                                if (subl.equals(l)) {
                                                    // it is an overlap at root position, so test for trivial critical pair
                                                    if (usable.equals(l_to_r)) {
                                                        // situation is not critical
                                                    } else {
                                                        final TRSSubstitution delta = u.getMgu();
                                                        if (r.applySubstitution(delta).equals(usable.getRhsInStandardRepresentation().applySubstitution(delta))) {
                                                            // trivial critical pair, not critical for rewriting processor
                                                        } else {
                                                            // non-trivial critical pair
                                                            continue subterms;
                                                        }
                                                    }
                                                } else {
                                                    // overlap below root, maybe uncritical but we do not test on
                                                    // trivial critical pairs here
                                                    continue subterms;
                                                }
                                            }
                                        }
                                    }
                                }

                            }

                            final Position p = posWithSub.x;

                            final Set<Rule> newRules = new LinkedHashSet<>(1);
                            final Set<Pair<Rule, Rule>> resRules = new LinkedHashSet<>(1);
                            final Rule generatedSToNewT =
                                Rule.create(s, t.replaceAt(p, rule.getRight().applySubstitution(matcher)));
                            final Rule sToNewT = qdp.getPair(generatedSToNewT);
                            newRules.add(sToNewT);
                            resRules.add(new Pair<>(generatedSToNewT, sToNewT));

                            boolean complete = true;
                            final Iterator<? extends TRSTerm> i = sub.getArguments().iterator();
                            while (complete && i.hasNext()) {
                                complete = usableRules.getQRNormal(Rule.create(s, i.next()));
                            }

                            if (this.beComplete && !complete) {
                                // okay, do not use incomplete technique
                                continue;
                            }
                            final Triple<Position, Set<Rule>, Rule> triple = new Triple<>(p, localUsableRules, rule);
                            return new Quadruple<>(null, complete ? YNMImplication.EQUIVALENT : YNMImplication.SOUND,
                                resRules, triple);
                        }
                    }
                }
            }


        }

        return null;


    }

    public static class Arguments extends QDPTransformationProcessor.Arguments {
        public boolean beComplete = false;
    }
}
