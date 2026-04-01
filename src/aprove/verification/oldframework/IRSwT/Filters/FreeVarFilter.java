package aprove.verification.oldframework.IRSwT.Filters;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Removes all free variables, i.e., it deletes arguments until every variable already occurs on the left side.
 */
public class FreeVarFilter extends AbstractFilter {

    public FreeVarFilter(final Set<IGeneralizedRule> inputRules) {
        super(inputRules);
    }

    @Override
    protected LinkedHashSet<IGeneralizedRule> runFilter() {
        LinkedHashSet<IGeneralizedRule> currentRules = new LinkedHashSet<>(this.rules);
        LinkedHashSet<IGeneralizedRule> nextRules = null;

        //register history for all rules once:
        for (final IGeneralizedRule rule : currentRules) {
            this.registerOrigin(rule, rule);
        }

        boolean changed;
        do {
            changed = false;

            checking: for (final IGeneralizedRule iRule : currentRules) {
                final Set<TRSVariable> leftVars = iRule.getLeft().getVariables();
                final TRSTerm right = iRule.getRight();
                assert right instanceof TRSFunctionApplication;

                final TRSFunctionApplication rightFunc = (TRSFunctionApplication) right;

                for (int i = 0; i < rightFunc.getRootSymbol().getArity(); i++) {
                    final TRSTerm arg = rightFunc.getArgument(i);
                    final Set<TRSVariable> argVars = arg.getVariables();

                    if (!leftVars.containsAll(argVars)) {
                        nextRules = this.removeArg(currentRules, rightFunc.getRootSymbol(), i);
                        changed = true;
                        break checking;
                    }
                }
            }

            if (changed) {
                currentRules = nextRules;
            }

        } while (changed);

        return currentRules;
    }

    private LinkedHashSet<IGeneralizedRule> removeArg(final Set<IGeneralizedRule> currentRules,
        final FunctionSymbol rootSymbol,
        final int i) {
        final LinkedHashSet<IGeneralizedRule> nextRules = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : currentRules) {
            final TRSFunctionApplication left = rule.getLeft();
            final TRSTerm right = rule.getRight();
            assert right instanceof TRSFunctionApplication;
            final TRSFunctionApplication rightFunc = (TRSFunctionApplication) right;

            final TRSFunctionApplication newLeft = this.filterFunctionApplication(left, rootSymbol, i);
            final TRSFunctionApplication newRight = this.filterFunctionApplication(rightFunc, rootSymbol, i);

            final IGeneralizedRule nextRule = IGeneralizedRule.create(newLeft, newRight, rule.getCondTerm());
            nextRules.add(nextRule);

            // Update the history:
            LinkedList<IGeneralizedRule> oldRules = this.getOldRules(rule);
            if (oldRules == null) {
                oldRules = new LinkedList<>();
                oldRules.add(rule);
            } else {
                oldRules = new LinkedList<>(oldRules);
            }
            for (final IGeneralizedRule oldRule : oldRules) {
                this.registerOrigin(oldRule, nextRule);
            }
        }

        return nextRules;
    }

    private TRSFunctionApplication filterFunctionApplication(final TRSFunctionApplication f,
        final FunctionSymbol filterSymbol,
        final int i) {
        if (f.getRootSymbol().equals(filterSymbol)) {
            final ArrayList<TRSTerm> newArgs = new ArrayList<>(filterSymbol.getArity() - 1);
            for (int j = 0; j < filterSymbol.getArity(); j++) {
                if (j != i) {
                    newArgs.add(f.getArgument(j));
                }
            }
            final FunctionSymbol newSymbol = FunctionSymbol.create(filterSymbol.getName(), filterSymbol.getArity() - 1);
            return TRSTerm.createFunctionApplication(newSymbol, newArgs);
        } else {
            return f;
        }
    }

    @Override
    public TRSTerm filterTerm(final TRSTerm t) {
        return t;
    }

    @Override
    public boolean isFunctionSymbolKnown(FunctionSymbol f) {
	throw new RuntimeException("change is term-dependend");
    }
}
