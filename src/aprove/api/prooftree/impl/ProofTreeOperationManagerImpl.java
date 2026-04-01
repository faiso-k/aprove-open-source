package aprove.api.prooftree.impl;

import java.util.*;
import java.util.concurrent.atomic.*;

import aprove.api.prooftree.*;
import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.strategies.UserStrategies.*;

public class ProofTreeOperationManagerImpl implements ProofTreeOperationManager {

    private final AProVE aprove;
    private final Set<SubAprove> subAproves = new LinkedHashSet<>();
    private final AtomicInteger numberOfRunningOperations = new AtomicInteger(0);

    public ProofTreeOperationManagerImpl(AProVE aprove) {
        this.aprove = aprove;
    }

    public void runAprove(ProofResultHandler proofResultHandler) {
        run(aprove, proofResultHandler);
    }

    public void runSubAprove(List<BasicObligationNode> nodes,
                             UserStrategy userStrategy,
                             Timeout timeout,
                             ProofResultHandler proofResultHandler) {
        SubAprove subAprove = new SubAprove(this.aprove, nodes);
        this.subAproves.add(subAprove);
        if (!timeout.isInfinite()) {
            subAprove.setTimeout(timeout.getDurationOrThrow());
        }
        subAprove.setUserStrategy(userStrategy);
        run(subAprove, proofResultHandler);
    }

    private void run(ProveRunner runner, ProofResultHandler proofResultHandler) {
        numberOfRunningOperations.incrementAndGet();
        ProveRunnerExecutor.execute(this, runner, proofResultHandler, numberOfRunningOperations::decrementAndGet);
    }

    @Override
    public void stop() {
        for (SubAprove subAprove : subAproves) {
            subAprove.stop();
        }
        aprove.stop();
    }

    @Override
    public boolean isRunning() {
        return numberOfRunningOperations.get() != 0;
    }
}
