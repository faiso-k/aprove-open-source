package aprove.strategies.ExecutableStrategies;

import aprove.prooftree.Obligations.*;
import aprove.strategies.UserStrategies.*;

public class ExecWallTimer extends ExecSimple {

    private final long delay; // in milliseconds

    public ExecWallTimer(UserStrategy str, long delayInMillis, BasicObligationNode pos, RuntimeInformation rti) {
        super("ERealTimer", str, pos, rti);
        this.delay = delayInMillis;
        Thread delayThread = new Thread(new DelayTimer(), "delay thread");
        delayThread.setDaemon(true);
        delayThread.start();
    }

    private void finish() {
        this.asyncStop("WallTimer expired");
    }

    private class DelayTimer implements Runnable {
        @Override
        public void run() {
            try {
                Thread.sleep(ExecWallTimer.this.delay);
                ExecWallTimer.this.finish();
            } catch (InterruptedException e) {
                // Do nothing, then, I guess
            }
        }
    }
}
