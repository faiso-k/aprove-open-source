package aprove.verification.oldframework.IntTRS;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Common parent class for several argument filters, providing useful methods.
 *
 * @author Marc Brockschmidt
 */
public abstract class IntTRSArgumentFilter extends Processor.ProcessorSkeleton {
    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSLike;
    }

    /**
     * Remove the given arguments of all terms, construct a new rule set and
     * return it. In addition, information about renamed symbols is returned.
     * @param rules the rule set
     * @param removedPositions information about arguments that can be removed
     * @param takenSymbols the function symbols that are already in use and may
     * not be used again
     * @return a result with a new set of rules, a map from old to new function symbols (with smaller arity)
     */
    public static Pair<Set<IGeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> getResultingRules(
        final Set<IGeneralizedRule> rules,
        final CollectionMap<FunctionSymbol, Integer> removedPositions,
        final Collection<FunctionSymbol> takenSymbols,
        Map<IGeneralizedRule, IGeneralizedRule> oldNewMap)
    {
        // the rules of the new IntTRS
        final Set<IGeneralizedRule> newRules = new LinkedHashSet<>(rules.size());

        // helper for name generation
        final Map<FunctionSymbol, FunctionSymbol> names = new LinkedHashMap<>();

        // for uninteresting symbols do not change the name
        final Collection<FunctionSymbol> symbols = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : rules) {
            symbols.addAll(rule.getLeft().getFunctionSymbols());
            symbols.addAll(rule.getRight().getFunctionSymbols());
        }
        symbols.removeAll(removedPositions.keySet());
        for (final FunctionSymbol fs : symbols) {
            final boolean added = takenSymbols.add(fs);
            assert (added);
            names.put(fs, fs);
        }

        for (final IGeneralizedRule rule : rules) {
            final TRSFunctionApplication lhs = rule.getLeft();
            final TRSFunctionApplication newLhs =
                (TRSFunctionApplication) HelperClass.remove(
                    lhs,
                    removedPositions,
                    names,
                    takenSymbols,
                    IDPPredefinedMap.DEFAULT_MAP);
            final TRSTerm rhs = rule.getRight();
            TRSTerm newRhs;
            if (!rhs.isVariable()) {
                newRhs = HelperClass.remove(rhs, removedPositions, names, takenSymbols, IDPPredefinedMap.DEFAULT_MAP);
            } else {
                newRhs = rhs;
            }
            final IGeneralizedRule newRule = IGeneralizedRule.create(newLhs, newRhs, rule.getCondTerm());
            newRules.add(newRule);
            if (oldNewMap != null) {
                oldNewMap.put(rule, newRule);
            }
        }

        return new Pair<>(newRules, names);
    }
}
