package aprove.verification.oldframework.IRSwT.Engines;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.IRSwT.Orders.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Synthesizes some order that can be used to simplify a integer rewrite system with terms (IRSwT).
 * This is the abstract super class that defines methods to be implemented by every concrete engine.
 * @author Matthias Hoelzel
 *
 */
public abstract class AbstractOrderEngine {
    /** Set of rules to be considered. */
    protected final Set<IGeneralizedRule> rules;

    /** Dictionary of sorts. */
    protected final SortDictionary sortDictionary;

    /** Generates fresh names. */
    protected final FreshNameGenerator fng;

    /** Some aborter! */
    protected final Abortion aborter;

    /** Avoid unnecessary calculations. */
    private boolean executed = false;

    /** Result order. */
    private AbstractOrder result = null;

    /**
     * Constructor!
     * @param inputRules set of input rules, which are assumed to be variable disjoint
     * @param sorts sort dictionary
     * @param abortion some aborter
     * @param freshNameGenerator generates fresh names
     */
    public AbstractOrderEngine(
        final Set<IGeneralizedRule> inputRules,
        final SortDictionary sorts,
        final Abortion abortion,
        final FreshNameGenerator freshNameGenerator)
    {
        this.rules = inputRules;
        this.sortDictionary = sorts;
        this.fng = freshNameGenerator;
        this.aborter = abortion;
    }

    /**
     * Returns the synthesized order.
     * @return some order
     * @throws AbortionException can be aborted
     */
    public final AbstractOrder getOrder() throws AbortionException {
        if (!this.executed) {
            this.result = this.generateOrder();
            this.executed = true;
        }
        if (this.result != null) {
            assert this.result.getRules().equals(this.rules) : "";
            assert this.rules.containsAll(this.result.getStrictOrientedRules());
            assert this.rules.containsAll(this.result.getBoundedRules());
        }
        return this.result;
    }

    /**
     * Calculates the order. In case of failure it returns null.
     * @return should return the synthesized order
     * @throws AbortionException can be aborted
     */
    protected abstract AbstractOrder generateOrder() throws AbortionException;
}
