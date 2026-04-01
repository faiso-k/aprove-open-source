package aprove.verification.dpframework.DPConstraints;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public abstract class InfRule {
    protected InfRuleContext irc;
    int number;

    /**
     *
     * @param implication
     * @param aborter TODO
     * @return the result (a new implication) of the application of this rule,
     *         which replaces the implication if it is applicable, otherwise null
     * @throws AbortionException TODO
     */
    public Pair<Constraint, InfProofStepInfo> applyToImplication(final Implication implication, final Abortion aborter)
        throws AbortionException
    {
        return null;
    }

    /**
     * the InfRuleContext should register by this rule if it uses this rule
     * @param irc
     */
    public void initContext(final InfRuleContext irc) {
        this.irc = irc;
        this.number = irc.getNextRuleNumber();
    }

    /**
     * @return the context of this rule
     */
    public InfRuleContext getIrc() {
        return this.irc;
    }

    /**
     * @return the number of this rule in the context
     */
    public int getNumber() {
        return this.number;
    }

    /**
     * @return a short description string
     */
    public abstract String getName();

    /**
     * @return a longer description string
     */
    public abstract String getLongName();

    /**
     * @return the global id of this rule (as in the increasing paper)
     */
    public abstract InfRuleID getID();

    @Override
    public String toString() {
        return this.getName();
    }

}
