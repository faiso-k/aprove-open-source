package aprove.verification.oldframework.IRSwT.Engines;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.IRSwT.Filters.*;
import aprove.verification.oldframework.IRSwT.Orders.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.IRSwT.Utils.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Abstract class for term order generation.
 * @author Matthias Hoelzel
 */
public abstract class TermOrderEngine extends AbstractOrderEngine {
    /** We have to remove the arithmetic first. */
    protected Set<IGeneralizedRule> preparedRules;

    /** Stores the filter we used to prepare the rules. */
    protected AbstractFilter filter;

    /** Collects the new symbols. */
    protected SymbolNamesCollector symbolsAfterPreparation;

    /**
     * Constructor!
     * @param inputRules set of rules to be analyzed
     * @param sorts sort dictionary
     * @param abortion some aborter
     * @param freshNameGenerator some name generator
     */
    public TermOrderEngine(
        final Set<IGeneralizedRule> inputRules,
        final SortDictionary sorts,
        final Abortion abortion,
        final FreshNameGenerator freshNameGenerator)
    {
        super(inputRules, sorts, abortion, freshNameGenerator);
    }

    @Override
    final protected AbstractOrder generateOrder() throws AbortionException {
        this.prepare();
        return this.generateTermOrder();
    }

    /**
     * Prepares the rules by removing arithmetic and collects the symbols.
     * @throws AbortionException
     */
    private void prepare() throws AbortionException {
        this.filter = new RemoveIntFilter(this.rules, this.sortDictionary, this.fng);
        this.preparedRules = this.filter.applyFilter();
        this.symbolsAfterPreparation = new SymbolNamesCollector(this.preparedRules);
    }

    /**
     * Somehow generates a order
     * @return a order
     * @throws AbortionException can be aborted
     */
    protected abstract AbstractOrder generateTermOrder() throws AbortionException;
}
