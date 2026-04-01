package aprove.strategies.ExecutableStrategies.impl;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.Parameters.*;
import aprove.strategies.Util.*;

class RuntimeImplementation implements RuntimeInformation {
    private final RuntimeState state;

    /**
     * All accounting-to clocks, as an unmodifiable list.
     *
     * This list should usually have size ~0-2.
     */
    private final List<Clock> clocks;
    private final ThreadingPolicy policy;
    private final boolean checkProofs;

    private RuntimeImplementation(
        final List<Clock> clocks,
        final ThreadingPolicy policy,
        final RuntimeState state,
        final boolean checkProofs)
    {
        this.clocks = clocks;
        this.policy = policy;
        this.state = state;
        this.checkProofs = checkProofs;
    }

    static RuntimeInformation createInitial(final RuntimeState state, final boolean checkProofs) {
        return new RuntimeImplementation(Collections.<Clock>emptyList(), ThreadingPolicy.DEFAULT, state, checkProofs);
    }

    public static RuntimeInformation createBelow(
        final List<Clock> clocks,
        final RuntimeState state,
        final boolean checkProofs)
    {
        return new RuntimeImplementation(clocks, ThreadingPolicy.DEFAULT, state, checkProofs);
    }

    @Override
    public RuntimeInformation copyAddClock(final Clock clock) {
        List<Clock> newClocks = new ArrayList<Clock>(this.clocks.size() + 1);
        newClocks.addAll(this.clocks);
        newClocks.add(clock);
        newClocks = Collections.unmodifiableList(newClocks);
        return new RuntimeImplementation(newClocks, this.policy, this.state, this.checkProofs);
    }

    @Override
    public RuntimeInformation copyWithDifferentScheduling(final ThreadingPolicy policy) {
        return new RuntimeImplementation(this.clocks, policy, this.state, this.checkProofs);
    }

    @Override
    public List<aprove.strategies.Abortions.Clock> getClocks() {
        return this.clocks;
    }

    @Override
    public ThreadingPolicy getThreadingPolicy() {
        return this.policy;
    }

    @Override
    public Object getMetadata(final Metadata key) {
        return this.state.getMetadata(key);
    }

    @Override
    public StrategyProgram getProgram() {
        return this.state.program;
    }

    @Override
    public void execute() {
        this.state.execute();
    }

    @Override
    public boolean checkProofs() {
        return this.checkProofs;
    }
}
