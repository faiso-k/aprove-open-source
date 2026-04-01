/**
 *
 */
package aprove.verification.oldframework.IRSwT.Filters;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Replaces predefined arithmetic by a fresh constant symbol.
 * @author Matthias Hoelzel
 */
public class RemoveIntFilter extends SortFilter {
    /** Generates fresh names. */
    private final FreshNameGenerator fng;

    /** A constant term that represents remaining predefined arithmetic. */
    private final TRSFunctionApplication predefinedConstant;

    /**
     * Constructor!
     * @param inputRules some input rules
     * @param dictionary sort dictionary
     * @param gen some fresh name generator
     */
    public RemoveIntFilter(
        final Set<IGeneralizedRule> inputRules,
        final SortDictionary dictionary,
        final FreshNameGenerator gen)
    {
        super(inputRules, dictionary);
        this.fng = gen;

        final String predefinedName = this.fng.getFreshName("predef", false);
        final FunctionSymbol predefinedSymbol = FunctionSymbol.create(predefinedName, 0);
        this.predefinedConstant = TRSTerm.createFunctionApplication(predefinedSymbol);
    }

    @Override
    public TRSTerm filterTerm(final TRSTerm t) {
        if (t instanceof TRSFunctionApplication) {
            // Remove arguments that are always an integer:
            final TRSTerm noAlwaysInts = this.removeSort(t, Sort.INTEGER);
            assert noAlwaysInts instanceof TRSFunctionApplication : "Should be function application!";

            // Integer still might occur in EVERYTHING arguments:
            // Now we replace these by a fresh constant
            final TRSFunctionApplication func = (TRSFunctionApplication) noAlwaysInts;
            final FunctionSymbol sym = func.getRootSymbol();

            final ArrayList<TRSTerm> newArguments = new ArrayList<>();
            for (final TRSTerm arg : func.getArguments()) {
                newArguments.add(this.removePredefined(arg));
            }

            return TRSTerm.createFunctionApplication(sym, newArguments);
        } else {
            return t;
        }
    }

    /**
     * Replaces predefined arithmetic by the given term.
     * @param t term to be purged
     * @param predefinedTerm replacement for arithmetic
     * @return purged term
     */
    private TRSTerm removePredefined(final TRSTerm t) {
        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication f = (TRSFunctionApplication) t;
            final FunctionSymbol sym = f.getRootSymbol();
            if (IDPPredefinedMap.DEFAULT_MAP.isPredefined(sym)) {
                return this.predefinedConstant;
            } else {
                final ArrayList<TRSTerm> newArguments = new ArrayList<>();
                for (final TRSTerm a : f.getArguments()) {
                    newArguments.add(this.removePredefined(a));
                }
                return TRSTerm.createFunctionApplication(sym, newArguments);
            }
        } else {
            return t;
        }
    }

    @Override
    public String export(final Export_Util eu) {
        return eu.tttext("Removed predefined arithmetic.");
    }

    @Override
    protected IGeneralizedRule processRule(final IGeneralizedRule newRule) {
        return IGeneralizedRule.create(newRule.getLeft(), newRule.getRight(), null);
    }
}
