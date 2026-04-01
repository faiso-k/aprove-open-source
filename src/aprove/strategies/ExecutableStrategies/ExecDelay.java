package aprove.strategies.ExecutableStrategies;

import aprove.prooftree.Obligations.*;
import aprove.strategies.UserStrategies.*;

public class ExecDelay extends ExecutableStrategy {

    private final UserStrategy str;
    private final BasicObligationNode pos;
    private final long delay; // in milliseconds

    private boolean done;
    private boolean success;

    public ExecDelay(
        final UserStrategy str,
        final long delayInMillis,
        final BasicObligationNode pos,
        final RuntimeInformation rti)
    {
        super(rti);
        this.str = str;
        this.pos = pos;
        this.done = false;
        this.delay = delayInMillis;
        new Thread(new DelayTimer(), "delay thread").start();
    }

    @Override
    ExecutableStrategy exec() {
        if (this.done) {
            if (this.success) {
                return this.str.getExecutableStrategy(this.pos, this.rti);
            } else {
                return new Fail("Delay() interrupted");
            }
        } else {
            return null;

        }
    }

    @Override
    void stop(final String reason) {
        this.finish(false);
    }

    private synchronized void finish(final boolean success) {
        if (!this.done) {
            this.success = success;
            this.done = true;
            this.rti.execute();
        }
    }

    @Override
    public String toString() {
        return "EDelay(" + this.str + ", " + "someObl" + ")";
    }

    private class DelayTimer implements Runnable {

        @Override
        public void run() {
            boolean success = true;
            try {
                Thread.sleep(ExecDelay.this.delay);
            } catch (final InterruptedException e) {
                success = false;
            }
            ExecDelay.this.finish(success);
        }

    }

}
