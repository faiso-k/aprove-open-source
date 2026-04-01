package aprove.verification.oldframework.IRSwT.Filters;

import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Represents an abstract filter mechanism.
 * @author Matthias Hoelzel
 *
 */
public abstract class AbstractFilter implements Exportable {
    /** Set of rules. */
    protected Set<IGeneralizedRule> rules;

    /**
     * Maps the old rules to the new rules.
     * This maps must be completed by a concrete filter.
     * */
    private final LinkedHashMap<IGeneralizedRule, IGeneralizedRule> history;

    /**
     * Maps the new rules to the old rules.
     * Since this can be non-injective, we have to store
     * a list of original rules.
     * This maps must be completed by a concrete filter.
     * */
    private final LinkedHashMap<IGeneralizedRule, LinkedList<IGeneralizedRule>> inverseHistory;

    /** Set of result rules. */
    private LinkedHashSet<IGeneralizedRule> resultRules;

    /** True iff this has been applied. */
    private boolean executed;

    /**
     * Constructor!
     * @param inputRules set of input rules
     */
    public AbstractFilter(final Set<IGeneralizedRule> inputRules) {
        this.rules = inputRules;
        this.history = new LinkedHashMap<>();
        this.inverseHistory = new LinkedHashMap<>();
    }

    /**
     * Applies this filter and returns a set of filtered rules.
     * @return set of filtered rules
     * @throws AbortionException
     */
    public LinkedHashSet<IGeneralizedRule> applyFilter() throws AbortionException {
        if (!this.executed) {
            this.resultRules = this.runFilter();
            this.executed = true;
        }
        return this.resultRules;
    }

    /**
     * Returns true iff this filter has changed anything.
     * @return boolean
     */
    public boolean hasChanged() {
        for (final Entry<IGeneralizedRule, IGeneralizedRule> e : this.history.entrySet()) {
            if (!e.getKey().equals(e.getValue())) {
                return true;
            }
        }
        return false;
    }

    /**
     * Registers the oldRules produces newRule, when applying this filter.
     * @param oldRule some rule
     * @param newRule another rule
     */
    protected void registerOrigin(final IGeneralizedRule oldRule, final IGeneralizedRule newRule) {
        this.history.put(oldRule, newRule);
        if (!this.inverseHistory.containsKey(newRule)) {
            this.inverseHistory.put(newRule, new LinkedList<IGeneralizedRule>());
        }
        this.inverseHistory.get(newRule).add(oldRule);
    }

    /**
     * Returns the converted version of the given rule.
     * @param oldRule some old rule
     * @return returns the filtered version (only
     * @throws AbortionException
     */
    public IGeneralizedRule getNewRule(final IGeneralizedRule oldRule) throws AbortionException {
        if (!this.executed) {
            this.runFilter();
        }
        return this.history.get(oldRule);
    }

    /**
     * Returns a list of the original rules.
     * @param newRule some filtered rule
     * @return list of rules
     */
    public LinkedList<IGeneralizedRule> getOldRules(final IGeneralizedRule newRule) {
        return this.inverseHistory.get(newRule);
    }

    /**
     * Returns a list of the original rules.
     * @param newRules collection of filtered rules
     * @return list of rules
     */
    public LinkedHashSet<IGeneralizedRule> getOldRules(final Collection<IGeneralizedRule> newRules) {
        if (newRules == null) {
            return null;
        }
        final LinkedHashSet<IGeneralizedRule> result = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : newRules) {
            final LinkedList<IGeneralizedRule> rulesToAdd = this.getOldRules(rule);
            if (rulesToAdd == null) {
                return null;
            }

            result.addAll(rulesToAdd);
        }
        return result;
    }
    
    /**
     * converts a old rule into a new one
     * @param oldRule
     * @return
     */
    public IGeneralizedRule getOldRule(IGeneralizedRule oldRule) {
        return this.history.get(oldRule);
    }

    /**
     * Given a term, filters w.r.t. to some sort.
     * @param t some term
     * @return a filtered term
     */
    public abstract TRSTerm filterTerm(TRSTerm t);
    
    /**
     * Given a function symbol, indicates whether f is known to the filter
     * @param f
     * @return
     */
    public abstract boolean isFunctionSymbolKnown(FunctionSymbol f);

    /**
     * Executes this filter.
     * @return set of filtered rules
     * @throws AbortionException
     */
    protected abstract LinkedHashSet<IGeneralizedRule> runFilter() throws AbortionException;
    
    @Override
    public String export(final Export_Util eu) {
        return "";
    }
}
