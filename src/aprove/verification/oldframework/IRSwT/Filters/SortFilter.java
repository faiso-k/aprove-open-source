/**
 *
 */
package aprove.verification.oldframework.IRSwT.Filters;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Filters terms that are of the "wrong" sort.
 * @author Matthias Hoelzel
 */
public abstract class SortFilter extends AbstractFilter {
    /** Sort dictionary: maps symbols and positions to sorts. */
    protected final SortDictionary sortDictionary;

    /**
     * Constructor!
     * @param inputRules set of rules
     * @param dictionary some sort dictionary
     */
    public SortFilter(final Set<IGeneralizedRule> inputRules, final SortDictionary dictionary) {
        super(inputRules);
        this.sortDictionary = dictionary;
    }

    @Override
    protected LinkedHashSet<IGeneralizedRule> runFilter() throws AbortionException {
        final LinkedHashSet<IGeneralizedRule> resultRules = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : this.rules) {

            final TRSTerm cond = rule.getCondTerm();
            final TRSSubstitution condSubst;
            if (cond != null && !cond.isVariable()) {
                final Pair<TRSTerm, TRSSubstitution> cleanRes =
                    IntegerConstraintCleaner.clean(cond, false, false, AbortionFactory.create());
                condSubst = cleanRes.y;
            } else {
                condSubst = TRSSubstitution.EMPTY_SUBSTITUTION;
            }
            final TRSFunctionApplication left =
                (TRSFunctionApplication) this.filterTerm(rule.getLeft().applySubstitution(condSubst));
            final TRSTerm right = this.filterTerm(rule.getRight().applySubstitution(condSubst));
            final IGeneralizedRule newRule = IGeneralizedRule.create(left, right, rule.getCondTerm());
            final IGeneralizedRule resultRule = this.processRule(newRule);

            resultRules.add(resultRule);
            this.registerOrigin(rule, resultRule);
        }
        return resultRules;
    }

    /**
     * Some classes might want to post-process the produced rules.
     * @param newRule input rule
     * @return some post-processed rule
     */
    protected IGeneralizedRule processRule(final IGeneralizedRule newRule) {
        return newRule;
    }

    /**
     * Given a term, this will filter away every argument not of sort s.
     * @param t a term
     * @param s some sort
     * @return a filtered term
     */
    protected TRSTerm retainSort(final TRSTerm t, final Sort s) {
        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication func = (TRSFunctionApplication) t;
            final FunctionSymbol sym = func.getRootSymbol();
            if (!IDPPredefinedMap.DEFAULT_MAP.isPredefined(sym)) {
                final ArrayList<TRSTerm> newArguments = new ArrayList<>(sym.getArity());
                final ImmutableList<TRSTerm> oldArguments = func.getArguments();
                for (int p = 0; p < sym.getArity(); p++) {
                    if (this.sortDictionary.getSort(sym, p) == s) {
                        newArguments.add(this.retainSort(oldArguments.get(p), s));
                    }
                }
                final FunctionSymbol newSymbol = FunctionSymbol.create(sym.getName(), newArguments.size());
                return TRSTerm.createFunctionApplication(newSymbol, newArguments);
            }
        }
        return t;
    }

    /**
     * Given a term, this will filter away every argument not of sort s.
     * @param t a term
     * @param s some sort
     * @return a filtered term
     */
    protected TRSTerm removeSort(final TRSTerm t, final Sort s) {
        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication func = (TRSFunctionApplication) t;
            final FunctionSymbol sym = func.getRootSymbol();
            if (!IDPPredefinedMap.DEFAULT_MAP.isPredefined(sym)) {
                final ArrayList<TRSTerm> newArguments = new ArrayList<>(sym.getArity());
                final ImmutableList<TRSTerm> oldArguments = func.getArguments();
                for (int p = 0; p < sym.getArity(); p++) {
                    if (this.sortDictionary.getSort(sym, p) != s) {
                        newArguments.add(this.removeSort(oldArguments.get(p), s));
                    }
                }
                final FunctionSymbol newSymbol = FunctionSymbol.create(sym.getName(), newArguments.size());
                return TRSTerm.createFunctionApplication(newSymbol, newArguments);
            }
        }
        return t;
    }
    
    public boolean isFunctionSymbolKnown(FunctionSymbol f) {
	return this.sortDictionary.isFunctionSymbolKnown(f);
    }
}
