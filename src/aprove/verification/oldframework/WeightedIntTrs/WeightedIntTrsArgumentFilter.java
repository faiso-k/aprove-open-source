package aprove.verification.oldframework.WeightedIntTrs;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.JBCOptions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Common parent class for several argument filters.
 *
 * @author Jera Hensel
 */
public abstract class WeightedIntTrsArgumentFilter extends Processor.ProcessorSkeleton {

    public static class Arguments {
        boolean justPropagateFromLoopHeads = true;

        public static StaticOption<Boolean> cliPropagateLowerBounds = new StaticOption<>();
        private InstanceOption<Boolean> propagateLowerBounds = new InstanceOption<Boolean>(false, cliPropagateLowerBounds);

        public boolean propagateLowerBounds() {
            return propagateLowerBounds.get();
        }

        public void setPropagateLowerBounds(boolean b) {
            propagateLowerBounds.set(b);
        }

    }

    Arguments args;

    @ParamsViaArgumentObject
    public WeightedIntTrsArgumentFilter(Arguments args) {
        this.args = args;
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof AbstractWeightedIntTermSystem<?>;
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
    public static <T extends AbstractWeightedIntRule<T>> Pair<Set<T>, Map<FunctionSymbol, FunctionSymbol>> getResultingRules(
        final Set<T> rules,
        final CollectionMap<FunctionSymbol, Integer> removedPositions,
        final Collection<FunctionSymbol> takenSymbols)
    {
        // the rules of the new IntTRS
        final Set<T> newRules = new LinkedHashSet<>(rules.size());

        // helper for name generation
        final Map<FunctionSymbol, FunctionSymbol> names = new LinkedHashMap<>();

        // for uninteresting symbols do not change the name
        final Collection<FunctionSymbol> symbols = new LinkedHashSet<>();
        for (final T rule : rules) {
            symbols.addAll(rule.getFunctionSymbols());
        }
        symbols.removeAll(removedPositions.keySet());
        for (final FunctionSymbol fs : symbols) {
            final boolean added = takenSymbols.add(fs);
            assert (added);
            names.put(fs, fs);
        }

        for (final T rule : rules) {
            final TRSFunctionApplication lhs = rule.getLeft();
            final TRSFunctionApplication newLhs =
                (TRSFunctionApplication) HelperClass.remove(
                    lhs,
                    removedPositions,
                    names,
                    takenSymbols,
                    IDPPredefinedMap.DEFAULT_MAP);
            List<TRSFunctionApplication> newRhs = new ArrayList<>(rule.getRight().size());
            for (TRSFunctionApplication r : rule.getRight()) {
                newRhs.add((TRSFunctionApplication) HelperClass.remove(r, removedPositions, names, takenSymbols, IDPPredefinedMap.DEFAULT_MAP));
            }
            newRules.add(rule.copy(newLhs, newRhs));
        }

        return new Pair<>(newRules, names);
    }
}
