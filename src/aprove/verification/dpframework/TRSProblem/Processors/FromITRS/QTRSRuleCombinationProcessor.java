package aprove.verification.dpframework.TRSProblem.Processors.FromITRS;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import immutables.*;

/**
 * @author Marc Brockschmidt
 */
public class QTRSRuleCombinationProcessor extends QTRSProcessor {
    /**
     * @author Marc Brockschmidt
     */
    private class RuleCombinationProof extends Proof {
        /**
         * collection holding all performed rule merges.
         */
        private final Collection<Triple<Rule, Rule, Rule>> doneMerges;

        /**
         * Create a new proof.
         * @param merges collection holding all performed rule merges.
         */
        public RuleCombinationProof(
                final Collection<Triple<Rule, Rule, Rule>> merges) {
            this.doneMerges = merges;
        }

        /**
         * @return the proof as a nice string representation.
         * @param eu an export util helping with formatting.
         * @param level not used.
         */
        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder sb =
                new StringBuilder();
            sb.append(eu.linebreak());
            final List<String> entries = new LinkedList<String>();
            for (final Triple<Rule, Rule, Rule> t : this.doneMerges) {
                final Rule left = t.x;
                final Rule right = t.y;
                final Rule merged = t.z;
                final String leftHTML = left.export(eu);
                final String rightHTML = right.export(eu);
                final String mergedHTML = merged.export(eu);
                entries.add("Merged the following two rules, obtaining the third:"
                        + eu.linebreak()
                        + leftHTML + eu.linebreak()
                        + rightHTML + eu.linebreak()
                        + mergedHTML + eu.linebreak());
            }
            sb.append(eu.set(entries, Export_Util.ITEMIZE));
            return sb.toString();
        }
    }
    /**
     * Yes, we can.
     * @param qtrs any qtrs
     * @return true
     */
    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        return true;
    }

    /**
     * Start working on the given QTRS.
     * @param qtrs some qtrs
     * @param aborter an aborter
     * @return the QTRS with duplicates removed (together with a proof and such)
     * @param rti don't know
     * @throws AbortionException never.
     */
    @Override
    protected Result processQTRS(final QTRSProblem qtrs,
        final Abortion aborter,
        final RuntimeInformation rti)
            throws AbortionException {
        final Collection<Triple<Rule, Rule, Rule>> doneMerges =
            new LinkedList<Triple<Rule, Rule, Rule>>();
        final ImmutableSet<Rule> oldRules = qtrs.getR();
        final QTermSet q = qtrs.getQ();
        final Set<Rule> newRules = QTRSRuleCombinationProcessor.combineRules(oldRules, q, doneMerges);

        if (newRules.size() == oldRules.size()) {
            return ResultFactory.unsuccessful();
        }

        final QTRSProblem newQtrs =
            QTRSProblem.create(ImmutableCreator.create(newRules), qtrs.getQ());

        final RuleCombinationProof proof =
            new RuleCombinationProof(doneMerges);
        return ResultFactory.proved(newQtrs, YNMImplication.SOUND, proof);
    }


    /**
     * Use rule combination to reduce the number of rules.
     * @param rules set to combine
     * @param q Q - who would have guessed?
     * @param doneMerges collection holding all performed rule merges.
     * @return New rule set
     */
    public static Set<Rule> combineRules(final ImmutableSet<Rule> rules,
            final QTermSet q,
            final Collection<Triple<Rule, Rule, Rule>> doneMerges) {
        boolean changed = false;
        final Set<Rule> currentRules =
            new LinkedHashSet<Rule>(rules);
        do {
            changed = false;

            /*
             * rightRules maps each function symbol to the set of rules
             * which have that symbol as root symbol on the left hand side, i.e.,
             * which may rewrite terms with that symbol and thus can be used
             * as right side for our combination.
             *
             * leftRules maps each function symbol to the set of rules
             * which have that symbol _somewhere_ on the right hand side, so
             * that this symbol may be rewritten and the rule can be used on
             * the left hand side.
             */
            final CollectionMap<FunctionSymbol, Rule> rightRulesMap =
                new CollectionMap<FunctionSymbol, Rule>();
            final CollectionMap<FunctionSymbol, Rule> leftRulesMap =
                new CollectionMap<FunctionSymbol, Rule>();

            // Fill rightRules and leftRules
            QTRSRuleCombinationProcessor.updateRuleMaps(currentRules, rightRulesMap, leftRulesMap);

            final Collection<FunctionSymbol> definedSymbols =
                new LinkedList<FunctionSymbol>(leftRulesMap.keySet());
            for (final FunctionSymbol fs : definedSymbols) {
                changed |= QTRSRuleCombinationProcessor.tryToRemoveSymbol(fs, currentRules, q, rightRulesMap, leftRulesMap, doneMerges);
            }
        } while (changed);

        return currentRules;
    }

    /**
     * Try to remove function symbol fs by combining all rules using it.
     *
     * @param fs Function symbol to remove
     * @param rules Rule set to look into
     * @param q Q - who would have guessed?
     * @param rightRulesMap maps each function symbol to the set of rules
     *  which have that symbol as root symbol on the left hand side
     * @param leftRulesMap maps each function symbol to the set of rules
     *  which have that symbol as root symbol on the right hand side
     * @param doneMerges collection holding all performed rule merges.
     * @return true iff the symbol could be removed.
     */
    private static boolean tryToRemoveSymbol(final FunctionSymbol fs,
            final Set<Rule> rules,
            final QTermSet q,
            final CollectionMap<FunctionSymbol, Rule> rightRulesMap,
            final CollectionMap<FunctionSymbol, Rule> leftRulesMap,
            final Collection<Triple<Rule, Rule, Rule>> doneMerges) {
        final Collection<Rule> leftRules =
            new LinkedHashSet<Rule>(leftRulesMap.getNotNull(fs));
        final Collection<Rule> rightRules =
            new LinkedHashSet<Rule>(rightRulesMap.getNotNull(fs));
        final Collection<Triple<Rule, Rule, Rule>> merges =
            new LinkedList<Triple<Rule, Rule, Rule>>();
        /*
         * We create one rule for each element of leftRules \times rightRules.
         * If both are bigger than one, removing this symbol would only increase
         * the size of the TRS, so don't do it.
         */
        if (leftRules.size() > 1 && rightRules.size() > 1) {
            return false;
        }
        final Set<Rule> newRules = new LinkedHashSet<Rule>();

        final Collection<FunctionSymbol> definedSymbols = leftRulesMap.keySet();

        // Iterate over rule pairs using the pair on left (resp. right) hand side:
        for (final Rule l : leftRules) {
            final Rule left = l.getWithRenumberedVariables("left");

            //Search for the position of the subterm matching the symbol to remove:
            final TRSFunctionApplication leftRight = (TRSFunctionApplication) left.getRight();

            TRSTerm leftRightSubterm = null;
            Position leftRightPos = null;
            if (leftRight.getRootSymbol().equals(fs)) {
                leftRightPos = Position.create();
                leftRightSubterm = leftRight;
            } else {
                for (final Pair<Position, TRSTerm> p : leftRight.getPositionsWithSubTerms()) {
                    final TRSTerm t = p.y;
                    if (t instanceof TRSFunctionApplication
                            && ((TRSFunctionApplication) t).getRootSymbol().equals(fs)) {
                        leftRightSubterm = t;
                        leftRightPos = p.x;
                        break;
                    }
                }
            }

            for (final Rule r : rightRules) {
                /*
                 * We do not want to combine a rule with itself, it may lead to
                 * infinitely many loop iterations
                 */
                if (l.equals(r)) {
                    newRules.add(l);
                    continue;
                }

                /*
                 * Rename and unify the left hand side of the right rule and
                 * the right hand side of the left rule
                 */
                final Rule right = r.getWithRenumberedVariables("right");
                final TRSFunctionApplication rightLeft = right.getLeft();

                if (left.getLeft().getRootSymbol().equals(rightLeft.getRootSymbol())) {
                    return false;
                }

                final Unification unification = new Unification(leftRightSubterm, rightLeft);
                final TRSSubstitution mgu = unification.getMgu();

                // If there is no mgu, then we cannot combine these rules
                if (mgu == null) {
                    return false;
                }

                final TRSTerm instantiatedRightLeft = rightLeft.applySubstitution(mgu);
                final TRSTerm instantiatedRightRight = right.getRight().applySubstitution(mgu);
                final TRSTerm renamedInstantiatedRightRight = instantiatedRightRight.renumberVariables("new");

                //If we can use the same rule to narrow over and over again: don't.
                for (final TRSTerm subterm : renamedInstantiatedRightRight.getSubTerms()) {
                    if (subterm.isVariable() || subterm == renamedInstantiatedRightRight) {
                        continue;
                    }
                    final Unification leftRightLeftUnif = new Unification(subterm, r.getLeft());
                    if (leftRightLeftUnif.getMgu() != null) {
                        return false;
                    }
                }

                // Check if all subterms of the instantiated rightLeft are
                // actually in normal form:
                if (!instantiatedRightLeft.isVariable()) {
                    final TRSFunctionApplication instRightLeftFa =
                        (TRSFunctionApplication) instantiatedRightLeft;
                    for (final TRSTerm arg : instRightLeftFa.getArguments()) {
                        if (q.canBeRewritten(arg)) {
                            return false;
                        }
                    }
                }

                /*
                 * We do not allow the matcher to contain defined symbols.
                 * Example: f(s(x)) -> g(f(s(x), x), g(y, x) -> f(x)
                 */
                for (final TRSTerm t : mgu.toMap().values()) {
                    final Set<FunctionSymbol> usedSymbols = t.getFunctionSymbols();
                    usedSymbols.retainAll(definedSymbols);
                    if (!usedSymbols.isEmpty()) {
                        return false;
                    }
                }
                final TRSFunctionApplication leftLeft = left.getLeft();

                // Generate a new rule
                final Rule newRule =
                    Rule.create(
                            leftLeft.applySubstitution(mgu),
                            leftRight.applySubstitution(mgu).replaceAt(
                                    leftRightPos,
                                    instantiatedRightRight))
                                    .getWithRenumberedVariables("x");

                newRules.add(newRule);
                merges.add(new Triple<Rule, Rule, Rule>(left, right, newRule));
            }
        }

        final Set<Rule> oldRules = new LinkedHashSet<Rule>(leftRules);
        oldRules.addAll(rightRules);

        if (newRules.size() == 0 || oldRules.containsAll(newRules)) {
            return false;
        }

        //If we didn't return until now, combining was successful. Update all data:
        rules.removeAll(oldRules);
        rules.addAll(newRules);
        doneMerges.addAll(merges);

        // Unregister each rule l -> r \in leftRules from rightRulesMap(root(l))
        for (final Rule rule : leftRules) {
            rightRulesMap.remove(rule.getLeft().getRootSymbol(), rule);

            for (final TRSTerm t : rule.getRight().getSubTerms()) {
                if (t instanceof TRSFunctionApplication) {
                    final TRSFunctionApplication fa = (TRSFunctionApplication) t;
                    leftRulesMap.remove(fa.getRootSymbol(), rule);
                }
            }
        }

        /*
         * Unregister each rule l -> r \in rightRules from leftRulesMap(f) for
         * all defined symbols f in r:
         */
        for (final Rule rule : rightRules) {
            final TRSFunctionApplication rhs = (TRSFunctionApplication) rule.getRight();
            leftRulesMap.remove(rhs.getRootSymbol(), rule);

            for (final TRSTerm t : rule.getRight().getSubTerms()) {
                if (t instanceof TRSFunctionApplication) {
                    final TRSFunctionApplication fa = (TRSFunctionApplication) t;
                    //If this is a defined symbol, we should unregister it:
                    leftRulesMap.remove(fa.getRootSymbol(), rule);
                }
            }
        }

        leftRulesMap.remove(fs);
        rightRulesMap.remove(fs);

        // Register the newly created rules
        QTRSRuleCombinationProcessor.updateRuleMaps(newRules, rightRulesMap, leftRulesMap);

        return true;
    }

    /**
     * Update the rule maps <code>rightRulesMap</code> and <code>leftRulesMap
     * </code> to entries for the rules from <code>rules</code>.
     * @param rules Some set of rules
     * @param rightRulesMap maps each function symbol to the set of rules
     *  which have that symbol as root symbol on the left hand side
     * @param leftRulesMap maps each function symbol to the set of rules
     *  which have that symbol as root symbol on the right hand side
     */
    private static void updateRuleMaps(
            final Collection<Rule> rules,
            final CollectionMap<FunctionSymbol, Rule> rightRulesMap,
            final CollectionMap<FunctionSymbol, Rule> leftRulesMap) {

        //Get all defined symbols:
        for (final Rule rule : rules) {
            final TRSFunctionApplication lhs = rule.getLeft();
            rightRulesMap.add(lhs.getRootSymbol(), rule);
        }

        //For all rhs, search for subterms:
        for (final Rule rule : rules) {
            if (rule.getRight().isVariable()) {
                continue;
            }

            final TRSFunctionApplication rhs = (TRSFunctionApplication) rule.getRight();
            leftRulesMap.add(rhs.getRootSymbol(), rule);

            for (final TRSTerm t : rule.getRight().getSubTerms()) {
                if (t instanceof TRSFunctionApplication) {
                    final TRSFunctionApplication fa = (TRSFunctionApplication) t;
                    //If this is a defined symbol, add it to our map:
                    if (rightRulesMap.containsKey(fa.getRootSymbol())) {
                        leftRulesMap.add(fa.getRootSymbol(), rule);
                    }
                }
            }
        }
    }
}
