package aprove.strategies.ExecutableStrategies.impl;

import aprove.*;
import aprove.strategies.ExecutableStrategies.*;

class Handle implements StrategyExecutionHandle {
    final Integer id;

    // null = not finished, non-null = finished due to reason in variable
    // Field protected by this object's monitor.
    private String finished;
    private ExecutableStrategy normalForm;
    private DefaultMachine machineImpl;

    Handle(DefaultMachine machineImpl, Integer id) {
        this.id = id;
        this.finished = null;
        this.machineImpl = machineImpl;
    }

    @Override
    public void stop(String reason) {
        this.machineImpl.stop(this.id, reason);
    }

    void setFinished(String reason, ExecutableStrategy str) {
        if (Globals.useAssertions) {
            assert(reason != null);
        }
        synchronized(this) {
            this.finished = reason;
            if (str != null && str.isNormal()) {
                this.normalForm = str;
            }
            this.notifyAll();
        }
    }

    @Override
    public synchronized void waitForFinish() throws InterruptedException {
        while(this.finished == null) {
            this.wait();
        }
    }

    @Override
    public synchronized boolean waitForFinish(long millis) throws InterruptedException {
        long currentTime = System.currentTimeMillis();
        long goalTime = currentTime + millis;
        while (this.finished == null && currentTime < goalTime) {
            long toWait = goalTime - currentTime;
            this.wait(toWait);
            currentTime = System.currentTimeMillis();
        }
        return (this.finished != null);
    }

    @Override
    public synchronized boolean isFinished() {
        return this.finished != null;
    }

    @Override
    public ExecutableStrategy getResult() {
        return this.normalForm;
    }
}
