package aprove.verification.dpframework.DPConstraints.idp;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
* TODO
* @author mpluecke
* @version $Id$
*/
public class InfRuleRewriting extends InfRuleConstraintRepl<Object> {

    /**
     * @param mode TODO
     */
    public InfRuleRewriting(Mode mode) {
        super(mode);
    }

    @Override
    protected Constraint processConstraint(
        Implication origImplication,
        Constraint constraint,
        boolean isConclusion,
        Object data,
        Abortion aborter
    ) throws AbortionException {
        if (constraint.isReducesTo()) {
            final ReducesTo reducesTo = (ReducesTo) constraint;
            if (
                reducesTo.getCount().getRewriting() >= this.irc.getRewritingCount() || reducesTo.getLeft().isVariable()
            ) {
                return reducesTo;
            }
            final IDPProblem idp = ((IdpInductionCalculus) this.irc).getIdp();

            final CriticalPairs critPairs = idp.getRuleAnalysis().getRAnalysis().getCriticalPairs();
            final boolean nonOverlapping = critPairs.isNonOverlapping(aborter);
            final boolean confluent = nonOverlapping || critPairs.isInnermostConfluent(aborter);

            // determine redexes // perhaps cache these results

            final Map<FunctionSymbol, ImmutableSet<GeneralizedRule>> ruleMap =
                idp.getRuleAnalysis().getRAnalysis().getRuleMap();

            final TRSTerm t = reducesTo.getLeft();
            // stolen from QDPRewritingProcessor
            subterms: for (Pair<Position, TRSTerm> posWithSub : t.getPositionsWithSubTerms()) {

                final TRSTerm subTerm = posWithSub.y;
                if (!subTerm.isVariable()) {
                    final TRSFunctionApplication sub = (TRSFunctionApplication) subTerm;
                    final Set<GeneralizedRule> possibleRules = ruleMap.get(sub.getRootSymbol());
                    if (possibleRules != null) {
                        for (GeneralizedRule rule : possibleRules) {
                            TRSSubstitution matcher = rule.getLeft().getMatcher(subTerm);
                            if (matcher != null) {
                                // okay, we can rewrite

                                // let us check non-overlappingness
                                if (nonOverlapping) {
                                    // there is nothing to do in this case
                                } else {
                                    final IUsableRulesEstimation usableRules =
                                        idp.getRuleAnalysis().getUseableRulesEstimation(null);
                                    final IdpQUsableRules usableActive = usableRules.getActiveConditions(reducesTo.getLeft());
                                    final Set<GeneralizedRule> localUsableRules = usableActive.getActive().keySet();
                                    if (confluent) {
                                        // okay, we get confluence for free
                                    } else {
                                        // check confluence of usable rules by demanding that root crit pairs are trivial
                                        final AbortableIterator<ImmutableTriple<TRSTerm, TRSTerm, Boolean>> critPairIterator =
                                            new IdpCritPairsIterator(localUsableRules);
                                        while (critPairIterator.hasNext(aborter)) {
                                            final ImmutableTriple<TRSTerm, TRSTerm, Boolean> critPair =
                                                critPairIterator.next(aborter);
                                            if (critPair.z && !critPair.x.equals(critPair.y)) {
                                                // critical root-overlap
                                                continue subterms; // thus, we cannot ensure confluence
                                            }
                                        }
                                    }

                                    // now we have to check that l -> r does only have trivial critical pairs with
                                    // usable rules
                                    final GeneralizedRule l_to_r =
                                        rule.getWithRenumberedVariables(TRSTerm.SECOND_STANDARD_PREFIX);
                                    final TRSTerm r = l_to_r.getRight();
                                    final TRSFunctionApplication l = l_to_r.getLeft();
                                    for (TRSFunctionApplication subl : l.getNonVariableSubTerms()) {
                                        final FunctionSymbol f = subl.getRootSymbol();
                                        for (GeneralizedRule usable : localUsableRules) {
                                            if (usable.getRootSymbol().equals(f)) {
                                                final Unification u =
                                                    new Unification(subl, usable.getLhsInStandardRepresentation());
                                                if (u.unify()) {
                                                    // we have detected an overlap
                                                    if (subl.equals(l)) {
                                                        // it is an overlap at root position, so test for trivial
                                                        // critical pair
                                                        if (usable.equals(l_to_r)) {
                                                            // situation is not critical
                                                        } else {
                                                            final TRSSubstitution delta = u.getMgu();
                                                            if (
                                                                r.applySubstitution(
                                                                    delta
                                                                ).equals(
                                                                    usable
                                                                    .getRhsInStandardRepresentation()
                                                                    .applySubstitution(delta)
                                                                )
                                                            ) {
                                                                // trivial critical pair, not critical for rewriting
                                                                // processor
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
                                final Set<TRSVariable> unboundedVars = rule.getUnboundedVariables();
                                if (!unboundedVars.isEmpty()) {
                                    final Map<TRSVariable, TRSTerm> match =
                                        new LinkedHashMap<TRSVariable, TRSTerm>(matcher.toMap());
                                    boolean changed = false;
                                    for (TRSVariable var : unboundedVars) {
                                        final TRSVariable newVar = this.irc.getFreshVariable(var);
                                        if (newVar != var) {
                                            match.put(var, newVar);
                                            changed = true;
                                        }
                                    }
                                    if (changed) {
                                        matcher = TRSSubstitution.create(ImmutableCreator.create(match));
                                    }
                                }
                                return ReducesTo.create(
                                    t.replaceAt(p, rule.getRight().applySubstitution(matcher)),
                                    reducesTo.getRight(),
                                    reducesTo.getParentFunc(),
                                    reducesTo.getCount().incRewriting(),
                                    reducesTo.getId());
                            }
                        }
                    }
                }
            }
        }
        return constraint;
    }

    @Override
    public InfRuleID getID() {
        return InfRuleID.REWRITING;
    }

    @Override
    public String getLongName() {
        return "Inf rule rewriting: rewrite lhs whenever possible";
    }

    @Override
    public String getName() {
        return "Rewriting";
    }

    @Override
    protected Object prepare(Implication implication, Abortion aborter) {
        return null;
    }

}
