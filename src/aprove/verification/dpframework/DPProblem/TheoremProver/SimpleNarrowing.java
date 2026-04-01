package aprove.verification.dpframework.DPProblem.TheoremProver;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * This class is supposed to use a simple narrowing procedure on an input set of
 * conditional rules
 *
 * @author micpar
 * @version $Id$
 */

public class SimpleNarrowing {

    /*
     * attributes
     */
    private SortCalculator sortCalculator = null;
    private final NameManager nameManager;
    private final TRSFunctionApplication myfalse;
    private final TRSFunctionApplication mytrue;

    private final int MAX_NARROWING_STEPS = 5;

    /**
     * @param sortCalculator,
     *            which encapsulates all sorts
     */
    public SimpleNarrowing(final SortCalculator sortCalculator, final NameManager nameManager) {
        super();
        this.sortCalculator = sortCalculator;
        this.myfalse = nameManager.getFalseApp();
        this.mytrue = nameManager.getTrueApp();
        this.nameManager = nameManager;
    }

    /**
     * @param condRules,
     *            a set of conditional rules which have to be narrowed down
     * @return the narrowed set
     */
    public ImmutableSet<ConditionalRule> narrowRules(final ImmutableSet<ConditionalRule> condRules) {
        // Compute indirect recursive rules
        ImmutableSet<ConditionalRule> indirectRules = this.computeIndirectRules(condRules);
        final Set<ConditionalRule> newRules = new LinkedHashSet<ConditionalRule>(condRules);
        int count = 0;
        // Repeat the narrowing steps if necessary, but do it maximal
        // MAX_NARROWING_STEPS times, since there are rules which cannot be
        // narrowed
        do {
            newRules.removeAll(indirectRules);
            for (final ConditionalRule condRule : indirectRules) {
                newRules.addAll(this.narrowRule(condRule, condRules));
            }
            indirectRules = this.computeIndirectRules(ImmutableCreator.create(newRules));
            count++;
        } while (!indirectRules.isEmpty() && count <= this.MAX_NARROWING_STEPS);
        return this.convertToAbsoluteDeterministic(ImmutableCreator.create(newRules));
    }

    /*
     * Convert the conditional rules to the absolute deterministic as needed by
     * theorem prover (cf. diploma thesis rabe)
     */
    private ImmutableSet<ConditionalRule> convertToAbsoluteDeterministic(final ImmutableSet<ConditionalRule> condRules) {
        final Set<ConditionalRule> newCondRules = new LinkedHashSet<ConditionalRule>();
        // Filter out not conditional rules, since these are
        // already in the right form
        for (final ConditionalRule condRule : condRules) {
            if (condRule.getConditions() == null) {
                newCondRules.add(condRule);
            }
            if (condRule.getConditions() != null && condRule.getConditions().isEmpty()) {
                newCondRules.add(condRule);
            }
        }
        // Compute set of rules which have to be changed
        final Set<ConditionalRule> rulesToBeChanged = new LinkedHashSet<ConditionalRule>(condRules);
        rulesToBeChanged.removeAll(newCondRules);
        final Set<ConditionalRule> temp = new LinkedHashSet<ConditionalRule>();
        // Collect rules l->r with the same l
        while (!rulesToBeChanged.isEmpty()) {
            final ConditionalRule rule = rulesToBeChanged.iterator().next();
            final Iterator<ConditionalRule> innerRuleIter = rulesToBeChanged.iterator();
            while (innerRuleIter.hasNext()) {
                final ConditionalRule innerRule = innerRuleIter.next();
                if (rule.getRule().getLeft().equals(innerRule.getRule().getLeft())) {
                    temp.add(innerRule);
                    innerRuleIter.remove();
                }
            }
            // Rearrange those rules and add them to the new rule set
            newCondRules.addAll(this.rearrangeConditions(ImmutableCreator.create(temp)));
            temp.clear();
        }

        return ImmutableCreator.create(newCondRules);
    }

    /*
     * Rearranges a set of conditional rules of the form cond_1 -> true,...,
     * cond_n -> true to the form cond_1' -> false,..., cond_m' -> false, cond_1 ->
     * true,..., cond_n -> true if the rule has similar rules, that is they have
     * the same l. The cond_i' are conditions from other similar rules. Thus we
     * ensure determinism
     */
    private ImmutableSet<ConditionalRule> rearrangeConditions(final ImmutableSet<ConditionalRule> condRules) {
        final Set<ConditionalRule> returnSet = new LinkedHashSet<ConditionalRule>();
        final List<Rule> invertedConds = new ArrayList<Rule>();
        // Collect conditions and invert them
        final Iterator<ConditionalRule> condRuleIter = condRules.iterator();
        while (condRuleIter.hasNext()) {
            ConditionalRule condRule = condRuleIter.next();
            if (!condRuleIter.hasNext()) {
                condRule = ConditionalRule.create(Rule.create(condRule.getLeft(), condRule.getRight()));
            }
            final List<Rule> newConditions = new ArrayList<Rule>();
            if (condRule.getConditions() != null) {
                newConditions.addAll(condRule.getConditions());
            }
            // Put the inverted conditions first as stated in literature
            newConditions.addAll(0, invertedConds);
            final ConditionalRule newCondRule =
                ConditionalRule.create(ImmutableCreator.create(newConditions), condRule.getRule());
            returnSet.add(newCondRule);
            if (condRuleIter.hasNext()) {
                // Invert all conditions of current rule here
                for (final Rule cond : condRule.getConditions()) {
                    final Rule invertedCond =
                        Rule.create(cond.getLeft(), cond.getRight().equals(this.mytrue) ? this.myfalse : this.mytrue);
                    invertedConds.add(invertedCond);
                }
            }
        }
        return ImmutableCreator.create(returnSet);
    }

    /*
     * Here we narrow down a conditional rule with a set of rules whose function
     * symbols occur in some place on the right hand side of the old rule
     */
    private ImmutableSet<ConditionalRule> narrowRule(final ConditionalRule oldRule,
        final ImmutableSet<ConditionalRule> condRules) {
        // Build a function symbol graph where the relations between the
        // function symbols are encapsulated. Conditions are ignored here.
        final SCCGraph<FunctionSymbol, Object> sccFunSymGraph =
            new SCCGraph<FunctionSymbol, Object>(new FunctionSymbolGraph(ConditionalRule.unwrap(condRules)));
        // Compute the function symbols occurring in the cycle of the root
        // symbol
        Set<FunctionSymbol> rootSymbolCycle = new LinkedHashSet<FunctionSymbol>();
        for (final Node<Cycle<FunctionSymbol>> node : sccFunSymGraph.getNodes()) {
            if (node.getObject().getNodeObjects().contains(oldRule.getRule().getRootSymbol())) {
                rootSymbolCycle = node.getObject().getNodeObjects();
                break;
            }
        }
        // Don't regard root symbol, narrowing with itself won't do anything
        rootSymbolCycle.remove(oldRule.getRule().getRootSymbol());
        Position minPos = null;
        // Compute the function symbol that occurs innermost left and is in the
        // same cycle as the root symbol
        for (final FunctionSymbol funSym : rootSymbolCycle) {
            if (oldRule.getRight().getFunctionSymbols().contains(funSym)) {
                if (minPos == null) {
                    minPos = this.computeInnermostLeftOccurrence(funSym, oldRule.getRight());
                } else {
                    minPos = this.getSmaller(minPos, this.computeInnermostLeftOccurrence(funSym, oldRule.getRight()));
                }
            }
        }
        // Get the subterm at this position, we know it is a function
        // application by design
        final TRSFunctionApplication funApp = (TRSFunctionApplication) oldRule.getRight().getSubterm(minPos);

        final Set<ConditionalRule> newRules = new LinkedHashSet<ConditionalRule>();
        for (final ConditionalRule condRule : condRules) {
            // If we find a rule which starts with the selected function symbol,
            // we create a new rule by putting the old rule and the found rule
            // together
            if (condRule.getLeft().getRootSymbol().equals(funApp.getRootSymbol())) {
                final ConditionalRule newCondRule = this.createNewConditionalRule(oldRule, condRule, minPos, funApp);
                // If one of the rules is the old rule, we know the narrowing
                // has failed and we return the old rule as new rule
                if (!newCondRule.equals(oldRule)) {
                    newRules.add(newCondRule);
                } else {
                    newRules.clear();
                    newRules.add(oldRule);
                    return ImmutableCreator.create(newRules);
                }
            }
        }
        return ImmutableCreator.create(newRules);
    }

    /*
     * Creates the new rule from the oldRule with a position on the right hand
     * side of the oldRule in which we can find the function application which
     * we have to replace with the right side of the rightRule
     */
    private ConditionalRule createNewConditionalRule(final ConditionalRule oldRule,
        ConditionalRule rightRule,
        final Position position,
        final TRSFunctionApplication funApp) {
        rightRule = rightRule.renameVars(oldRule.getRule().getVariables());
        // Try to match the left hand side of the rightRule on the funApp
        TRSSubstitution sigma = rightRule.getLeft().getMatcher(funApp);
        if (sigma != null) {
            // If we can find a matcher for the funApp we are happy and add the
            // new vars to the varmap
            this.addSubstitutedVarsToVarMap(sigma);
            // Apply the substitution everywhere
            final TRSFunctionApplication left = oldRule.getLeft().applySubstitution(sigma);
            final TRSTerm right = oldRule.getRight().replaceAt(position, rightRule.getRight().applySubstitution(sigma));
            // Make union of all conditions and apply substitution, check if
            // variable condition is violated, if yes quit and return oldRule
            final List<Rule> conditions = new ArrayList<Rule>();
            if (rightRule.getConditions() != null) {
                for (final Rule rule : rightRule.getConditions()) {
                    final Rule newCondition =
                        Rule.create(rule.getLeft().applySubstitution(sigma), rule.getRight().applySubstitution(sigma));
                    if (left.getVariables().containsAll(newCondition.getVariables())) {
                        conditions.add(newCondition);
                    } else {
                        return oldRule;
                    }
                }
            }
            if (oldRule.getConditions() != null) {
                for (final Rule rule : oldRule.getConditions()) {
                    final Rule newCondition =
                        Rule.create(rule.getLeft().applySubstitution(sigma), rule.getRight().applySubstitution(sigma));
                    if (left.getVariables().containsAll(newCondition.getVariables())) {
                        conditions.add(newCondition);
                    } else {
                        return oldRule;
                    }
                }
            }
            // Check variable condition, if violated exit with oldRule
            if (left.getVariables().containsAll(right.getVariables())) {
                return ConditionalRule.create(ImmutableCreator.create(conditions), Rule.create(left, right));
            } else {
                return oldRule;
            }
        } else {
            // Otherwise we have an argument clash, try to compute conditions
            // and substitution
            final List<Rule> conditions = new ArrayList<Rule>();
            sigma = TRSSubstitution.EMPTY_SUBSTITUTION;
            sigma = this.computeConditionsAndSubstitution(sigma, conditions, funApp, rightRule.getLeft());
            if (sigma != null) {
                // Add vars to varmap again
                this.addSubstitutedVarsToVarMap(sigma);
                // Apply substitution to conditions here
                final List<Rule> newConditions = new ArrayList<Rule>();
                for (final Rule cond : conditions) {
                    newConditions.add(Rule.create(cond.getLeft().applySubstitution(sigma),
                        cond.getRight().applySubstitution(sigma)));
                }
                // If there are no conditions create ConditionalRule without
                // conditions
                final TRSFunctionApplication left = oldRule.getLeft().applySubstitution(sigma);
                final TRSTerm right =
                    oldRule.getRight().replaceAt(position, rightRule.getRight()).applySubstitution(sigma);
                if (left.getVariables().containsAll(right.getVariables()) || right.getVariables().isEmpty()) {
                    if (newConditions.isEmpty()) {
                        return ConditionalRule.create(Rule.create(left, right));
                    } else {
                        return ConditionalRule.create(ImmutableCreator.create(newConditions), Rule.create(left, right));
                    }
                } else {
                    return oldRule;
                }
            }
            // Room for optimization here, narrow defined function inside if
            // possible
        }
        // Default case if all fails
        return oldRule;
    }

    /*
     * Compute argument-wise substitution and conditions
     */
    private TRSSubstitution computeConditionsAndSubstitution(TRSSubstitution sigma,
        final List<Rule> conditions,
        final TRSFunctionApplication left,
        final TRSFunctionApplication right) {
        // Bail out if someone calls the function in the wrong way
        if (sigma == null || conditions == null || left == null || right == null) {
            return null;
        }
        for (int arg = 0; arg < left.getArguments().size(); arg++) {
            // Try to unify arguments
            final TRSSubstitution sub = left.getArgument(arg).getMGU(right.getArgument(arg));
            if (sub != null) {
                // If it worked compose substitutions
                sigma = sigma.compose(sub);
            } else {
                // Otherwise create conditions
                // If we have the same root symbol, we can unpack it further
                if (((TRSFunctionApplication) left.getArgument(arg)).getRootSymbol().equals(
                    ((TRSFunctionApplication) right.getArgument(arg)).getRootSymbol())) {
                    if (this.computeConditionsAndSubstitution(sigma, conditions,
                        (TRSFunctionApplication) left.getArgument(arg), (TRSFunctionApplication) right.getArgument(arg)) == null) {
                        return null;
                    }
                } else {
                    // Right argument must be a constant, otherwise we can't do
                    // anything
                    if (((TRSFunctionApplication) right.getArgument(arg)).getRootSymbol().getArity() == 0) {
                        // CAUTION: Sorts MUST be regarded, create condition of
                        // form equal_sortN(left, right) -> true here
                        final String sortName =
                            this.sortCalculator.getFunOutputSortMap().get(
                                ((TRSFunctionApplication) right.getArgument(arg)).getRootSymbol()).getName();
                        final FunctionSymbol equal = this.nameManager.getEqualsSymbol(sortName);
                        final ArrayList<TRSFunctionApplication> args = new ArrayList<TRSFunctionApplication>(2);
                        args.add((TRSFunctionApplication) left.getArgument(arg));
                        args.add((TRSFunctionApplication) right.getArgument(arg));
                        final TRSFunctionApplication lefteq =
                            TRSTerm.createFunctionApplication(equal, ImmutableCreator.create(args));
                        conditions.add(Rule.create(lefteq, this.mytrue));
                    }
                    // Maybe room for optimization
                }
            }
        }
        return sigma;
    }

    /*
     * As the name suggests this method computes the innermost left occurrence
     * of a function symbol
     */
    private Position computeInnermostLeftOccurrence(final FunctionSymbol funSym, final TRSTerm right) {
        final Set<Position> positions = right.getPositions();
        final Iterator<Position> posIter = positions.iterator();
        // Compute positions at which the function symbol occurs
        while (posIter.hasNext()) {
            final Position pos = posIter.next();
            if (right.getSubterm(pos).isVariable()) {
                posIter.remove();
            } else {
                final TRSFunctionApplication funApp = (TRSFunctionApplication) right.getSubterm(pos);
                if (!funApp.getRootSymbol().equals(funSym)) {
                    posIter.remove();
                }
            }
        }
        // Now pick the longest left position of these
        Position minPos = null;
        for (final Position position : positions) {
            if (minPos == null) {
                minPos = position;
            } else {
                minPos = this.getSmaller(minPos, position);
            }
        }
        return minPos;
    }

    /*
     * Computes pos1 < pos2 Examples: 1234 < 123, 1234 < 1334, 234 < 12
     */
    private Position getSmaller(final Position pos1, final Position pos2) {
        if (pos1.getDepth() > pos2.getDepth()) {
            return pos1;
        } else if (pos2.getDepth() > pos1.getDepth()) {
            return pos2;
        } else {
            final int[] posarray1 = pos1.toIntArray();
            final int[] posarray2 = pos2.toIntArray();
            for (int index = 0; index < pos1.getDepth(); index++) {
                if (posarray1[index] < posarray2[index]) {
                    return pos1;
                } else if (posarray2[index] < posarray1[index]) {
                    return pos2;
                }
            }
        }
        return pos1;
    }

    /*
     * Computes the indirect recursive rules.
     */
    private ImmutableSet<ConditionalRule> computeIndirectRules(final ImmutableSet<ConditionalRule> allRules) {
        final Set<ConditionalRule> indirectRules = new LinkedHashSet<ConditionalRule>();
        // First filter out the direct and not recursive Rules
        final RuleAnalysis<Rule> analysis =
            new RuleAnalysis<Rule>(ImmutableCreator.create(ConditionalRule.unwrap(allRules)),
                IDPPredefinedMap.EMPTY_MAP);
        for (final ConditionalRule condRule : allRules) {
            // Filter out direct recursive rules and rules which are not
            // recursive at all
            if (!condRule.getRight().getFunctionSymbols().contains(condRule.getRule().getRootSymbol())
                && this.isRuleRecursive(condRule.getRule(), analysis)) {
                indirectRules.add(condRule);
            }
        }
        return ImmutableCreator.create(indirectRules);
    }

    /*
     * Decides wether a given rule is recursive
     */
    private boolean isRuleRecursive(final Rule rule, final RuleAnalysis<Rule> analysis) {
        // if a variable is on the right hand side, it should be clear
        if (rule.getRight().isVariable()) {
            return false;
        }
        // Compute the set of all defined functions on the right hand side
        final Set<FunctionSymbol> defSyms = new LinkedHashSet<FunctionSymbol>();
        defSyms.addAll(rule.getRight().getFunctionSymbols());
        defSyms.retainAll(analysis.getDefinedSymbols());
        if (defSyms.isEmpty()) {
            return false;
        }
        // Compute the defined symbols which lead to the root symbol again
        return this.isReachableFromItSelf(rule.getRootSymbol(), defSyms, analysis);
    }

    /*
     * Computes whether a given function symbol is reachable from a starting
     * function symbol set utilizing SCC graphs
     */
    private boolean isReachableFromItSelf(final FunctionSymbol funSym,
        final Set<FunctionSymbol> startFunSet,
        final RuleAnalysis<Rule> analysis) {
        // Build SCC graph
        final SCCGraph<FunctionSymbol, Object> sccFunSymGraph =
            new SCCGraph<FunctionSymbol, Object>(new FunctionSymbolGraph(analysis.getRules()));
        Set<Node<Cycle<FunctionSymbol>>> startNodeSet = new LinkedHashSet<Node<Cycle<FunctionSymbol>>>();
        // Compute start node set, i.e. set of nodes which contain the given
        // start function symbols
        for (final Node<Cycle<FunctionSymbol>> node : sccFunSymGraph.getNodes()) {
            for (final FunctionSymbol startSym : startFunSet) {
                if (node.getObject().getNodeObjects().contains(startSym)) {
                    startNodeSet.add(node);
                }
            }
        }
        // Determine the reachable nodes, if the function symbol is contained in
        // one of these we have recursion with function symbol
        startNodeSet = sccFunSymGraph.determineReachableNodes(startNodeSet);
        for (final Node<Cycle<FunctionSymbol>> node : startNodeSet) {
            if (node.getObject().getNodeObjects().contains(funSym)) {
                return true;
            }
        }
        return false;
    }

    /*
     * This method is important for the program initialization. It adds new
     * variables found by substitution to the sort maps. If we don't the program
     * initializer will fuck up.
     */
    private void addSubstitutedVarsToVarMap(final TRSSubstitution sigma) {
        // Get Domain
        for (final TRSVariable var : sigma.getDomain()) {
            // Get the variables which are assigned to the domainvar by sigma
            for (final TRSVariable rangeVar : sigma.toMap().get(var).getVariables()) {
                // If the map already contains the variable we are happy
                if (!this.sortCalculator.getVariableSortMap().containsKey(rangeVar)) {
                    // Get positions with variables
                    final List<Position> positions = sigma.toMap().get(var).getVariablePositions().get(rangeVar);
                    // Take first, because all vars of the same name have the
                    // same type
                    final Position pos = positions.iterator().next();
                    // If the position is the empty position get the sort of the
                    // replaced var
                    if (pos.equals(Position.create())) {
                        this.sortCalculator.addVariableToMap(rangeVar,
                            this.sortCalculator.getVariableSortMap().get(var));
                    } else {
                        // otherwise we look into the function symbol which
                        // encloses the var and take the according input sort
                        final TRSFunctionApplication funApp =
                            (TRSFunctionApplication) sigma.toMap().get(var).getSubterm(pos.shorten(1));
                        this.sortCalculator.addVariableToMap(
                            rangeVar,
                            this.sortCalculator.getFunInputSortMap().get(funApp.getRootSymbol()).get(
                                pos.toIntArray()[pos.getDepth() - 1]));
                    }
                }
            }
        }
    }

}
