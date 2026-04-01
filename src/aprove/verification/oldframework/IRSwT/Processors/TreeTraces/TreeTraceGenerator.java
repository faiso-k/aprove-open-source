package aprove.verification.oldframework.IRSwT.Processors.TreeTraces;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IRSwT.Filters.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Trivial enumeration algorithm for tree traces,
 * which are contained in a given IRSwT.
 * @author Matthias Hoelzel
 *
 */
public class TreeTraceGenerator {
    /**
     * Given input problem.
     */
    private final IRSwTProblem irswt;

    /**
     * Rule without integer arithmetik and without constant symbols.
     */
    private final ArrayList<IGeneralizedRule> preparedRules;

    /**
     * Name generator!
     */
    private final FreshNameGenerator ng;

    /**
     * Variable for eliminating constant symbols.
     */
    private final TRSVariable constantVar;

    /**
     * Maps prepared rules to arraylist of occuring variables.
     */
    private final LinkedHashMap<IGeneralizedRule, ArrayList<TRSVariable>> variables;

    /**
     * Maps prepared rules to indices of "surviving variables".
     */
    private final LinkedHashMap<IGeneralizedRule, Integer> variableIndices;

    /**
     * Maps prepared rules to the surviving variables. This allows a simpler notation!
     */
    private final LinkedHashMap<IGeneralizedRule, TRSVariable> toSurvive;

    /**
     * Maps prepared rules to tree trace rules.
     */
    private final LinkedHashMap<IGeneralizedRule, IGeneralizedRule> traceProposal;

    /**
     * Is set to true, when we found the tree traces.
     */
    private boolean done;

    /**
     * Constructor!
     * @param inputProblem some input IRSwT
     * @throws AbortionException can be aborted
     */
    public TreeTraceGenerator(final IRSwTProblem inputProblem) throws AbortionException {
        this.irswt = inputProblem;
        this.ng = this.irswt.createFreshNameGenerator();
        this.constantVar = TRSTerm.createVariable(this.ng.getFreshName("c", false));

        final RemoveIntFilter filter =
            new RemoveIntFilter(this.irswt.getRules(), (new SortAnalyzer(this.irswt.getRules())).analyze(), this.ng);
        final LinkedHashSet<IGeneralizedRule> filteredRules = filter.applyFilter();

        this.preparedRules = this.eliminateConstants(filteredRules);

        this.variables = new LinkedHashMap<>();
        this.variableIndices = new LinkedHashMap<>();

        for (final IGeneralizedRule rule : this.preparedRules) {
            this.variables.put(rule, new ArrayList<>(rule.getVariables()));
            this.variableIndices.put(rule, 0);
        }

        this.toSurvive = new LinkedHashMap<>();
        this.traceProposal = new LinkedHashMap<>();
    }

    /**
     * Replaces constant symbol c() by c(v) for a fixed fresh variable v.
     * @param filteredRules input rules
     * @return rules
     */
    private ArrayList<IGeneralizedRule> eliminateConstants(final LinkedHashSet<IGeneralizedRule> filteredRules) {
        final ArrayList<IGeneralizedRule> result = new ArrayList<>();
        for (final IGeneralizedRule rule : filteredRules) {
            final IGeneralizedRule newRule = this.eliminateConstants(rule);
            result.add(newRule);
        }
        return result;
    }

    /**
     * Replaces constant symbol c() by c(v) for a fixed fresh variable v.
     * @param rule input rule
     * @return rule
     */
    private IGeneralizedRule eliminateConstants(final IGeneralizedRule rule) {
        final TRSTerm newLeft = this.eliminateConstants(rule.getLeft());
        final TRSTerm newRight = this.eliminateConstants(rule.getRight());

        assert newLeft instanceof TRSFunctionApplication && newRight instanceof TRSFunctionApplication : "Expected some function application!";

        final IGeneralizedRule result = IGeneralizedRule.create((TRSFunctionApplication) newLeft, newRight, null);
        return result;
    }

    /**
     * Replaces constant symbol c() by c(v) for a fixed fresh variable v.
     * @param t input term
     * @return term
     */
    private TRSTerm eliminateConstants(final TRSTerm t) {
        if (t.isConstant()) {
            assert t instanceof TRSFunctionApplication : "Should be function application!";
            return TRSTerm.createFunctionApplication(
                FunctionSymbol.create(((TRSFunctionApplication) t).getRootSymbol().getName(), 1), this.constantVar);
        }
        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication f = (TRSFunctionApplication) t;
            final ArrayList<TRSTerm> args = new ArrayList<>();
            for (final TRSTerm oldArg : f.getArguments()) {
                args.add(this.eliminateConstants(oldArg));
            }
            return TRSTerm.createFunctionApplication(f.getRootSymbol(), args);
        } else {
            return t;
        }
    }

    /**
     * Produces the next trace.
     * @return tree trace
     */
    public TreeTrace generateNextTrace() {
        TreeTrace nextTrace = null;
        do {
            // 0. Any trace left?
            if (this.isDone()) {
                return null;
            }

            // 1. Try to produce the next trace
            nextTrace = this.produceNextTrace();

            // 2. Prepare the computation of next trace
            this.prepareNextTrace();

        } while (nextTrace == null);

        return nextTrace;
    }

    /**
     * Returns true, if we are done.
     * @return boolean
     */
    private boolean isDone() {
        return this.done;
    }

    /**
     * Private method producing the next trace.
     * @return tree trace
     */
    private TreeTrace produceNextTrace() {
        // 1. Calculate the "survival variables"
        for (final IGeneralizedRule rule : this.preparedRules) {
            final TRSVariable v = this.variables.get(rule).get(this.variableIndices.get(rule));
            assert v != null : "Variable should not be null!";
            this.toSurvive.put(rule, v);
        }

        // 2. Survival of the fittest arguments:
        for (final IGeneralizedRule rule : this.preparedRules) {
            this.traceProposal.put(rule, rule);
        }
        for (final IGeneralizedRule rule : this.preparedRules) {
            Pair<FunctionSymbol, Integer> evilPosition = null;
            do {
                evilPosition = this.tryToFindBadPosition(this.traceProposal.get(rule), this.toSurvive.get(rule));
                if (evilPosition != null && evilPosition.x.getArity() == 1) {
                    return null;
                } else if (evilPosition != null) {
                    this.removeBadPosition(evilPosition);
                }
            } while (evilPosition != null);
        }

        // 3. Collect the survivors:
        final LinkedHashSet<IGeneralizedRule> survivors = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : this.preparedRules) {
            survivors.add(this.traceProposal.get(rule));
        }
        return new TreeTrace(survivors);
    }

    /**
     * Tries to find a position which has to be eliminated.
     * @param rule input rule
     * @param v variable to survive
     * @return evil pair
     */
    private Pair<FunctionSymbol, Integer> tryToFindBadPosition(final IGeneralizedRule rule, final TRSVariable v) {
        final Pair<FunctionSymbol, Integer> evil = this.tryToFindBadPosition(rule.getLeft(), v);
        if (evil != null) {
            return evil;
        } else {
            return this.tryToFindBadPosition(rule.getRight(), v);
        }
    }

    /**
     * Tries to find a position which has to be eliminated.
     * @param t input term
     * @param v variable to survive
     * @return evil pair
     */
    private Pair<FunctionSymbol, Integer> tryToFindBadPosition(final TRSTerm t, final TRSVariable v) {
        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication f = (TRSFunctionApplication) t;
            for (int i = 0; i < f.getArguments().size(); i++) {
                final TRSTerm arg = f.getArgument(i);
                if (arg instanceof TRSVariable && !(v.equals(arg))) {
                    return new Pair<FunctionSymbol, Integer>(f.getRootSymbol(), i);
                } else {
                    final Pair<FunctionSymbol, Integer> evilResult = this.tryToFindBadPosition(arg, v);
                    if (evilResult != null) {
                        if (evilResult.x.getArity() == 1) {
                            return new Pair<FunctionSymbol, Integer>(f.getRootSymbol(), i);
                        } else {
                            return evilResult;
                        }
                    }
                }
            }
        }
        return null;
    }

    /**
     * Removes a certain argument of a certain symbol.
     * @param evilPosition evil pair
     */
    private void removeBadPosition(final Pair<FunctionSymbol, Integer> evilPosition) {
        for (final IGeneralizedRule rule : this.preparedRules) {
            final IGeneralizedRule oldRule = this.traceProposal.get(rule);
            final IGeneralizedRule newRule = this.removeBadPosition(oldRule, evilPosition);
            this.traceProposal.put(rule, newRule);
        }
    }

    /**
     * Removes a certain argument of a certain symbol.
     * @param oldRule input rule
     * @param evilPosition evil pair
     * @return rule
     */
    private IGeneralizedRule removeBadPosition(final IGeneralizedRule oldRule,
        final Pair<FunctionSymbol, Integer> evilPosition) {
        final TRSTerm l = this.removeBadPosition(oldRule.getLeft(), evilPosition);
        final TRSTerm r = this.removeBadPosition(oldRule.getRight(), evilPosition);

        assert l instanceof TRSFunctionApplication : "Should be function applicaton!";

        return IGeneralizedRule.create((TRSFunctionApplication) l, r, null);
    }

    /**
     * Removes a certain argument of a certain symbol.
     * @param t input term
     * @param evilPosition evil pair
     * @return rule
     */
    private TRSTerm removeBadPosition(final TRSTerm t, final Pair<FunctionSymbol, Integer> evilPosition) {
        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication f = (TRSFunctionApplication) t;
            final FunctionSymbol s = f.getRootSymbol();
            final ArrayList<TRSTerm> preparedArgs = new ArrayList<>();
            for (int i = 0; i < s.getArity(); i++) {
                if (!s.equals(evilPosition.x) || (i != evilPosition.y)) {
                    preparedArgs.add(this.removeBadPosition(f.getArgument(i), evilPosition));
                }
            }
            final FunctionSymbol newSymbol = FunctionSymbol.create(s.getName(), preparedArgs.size());
            return TRSTerm.createFunctionApplication(newSymbol, preparedArgs);
        } else {
            return t;
        }
    }

    /**
     * Prepare the state of this generator to produce the next tree trace.
     */
    private void prepareNextTrace() {
        int i = 0;
        boolean overflow = false;

        do {
            final IGeneralizedRule currentRule = this.preparedRules.get(i);
            final ArrayList<TRSVariable> currentVariables = this.variables.get(currentRule);
            final int currentIndex = this.variableIndices.get(currentRule);
            final int nextIndex = (currentIndex + 1) % currentVariables.size();
            this.variableIndices.put(currentRule, nextIndex);
            overflow = (nextIndex == 0);
            i++;
        } while (overflow && i < this.preparedRules.size());

        if (i == this.preparedRules.size() && overflow) {
            this.done = true;
        }
    }
}
