package aprove.strategies.Abortions;

import java.util.logging.*;

abstract class TrackProcess extends AbortionListener implements TimeTracker {
    private static final Logger log = Logger.getLogger(TrackProcess.class.getName());
    private static final boolean useLinuxTracker = TrackProcess.checkLinuxSupport();

    private static boolean checkLinuxSupport() {
        try {
            if (TrackProcessOnLinux.isSupported()) {
                return true;
            } else {
                TrackProcess.log.warning("Cannot find out cpu time on external processes, falling back to wall time!");
                return false;
            }
        } catch (final Throwable whatever) {
            TrackProcess.log.log(Level.WARNING, "Error trying to find out if I can get linux-style cpu time,"
                + " falling back to wall time!", whatever);
            return false;
        }
    }

    static TrackProcess create(final Process p, final Abortion abortion) {
        if (TrackProcess.useLinuxTracker) {
            return new TrackProcessOnLinux(abortion, p);
        } else {
            return new TrackProcessByWall(abortion, p);
        }
    }

    public static boolean canTrackByPID() {
        return TrackProcess.useLinuxTracker;
    }

    protected final Abortion abortion;

    public TrackProcess(final Abortion abortion) {
        this.abortion = abortion;
    }

    protected void start() {
        this.abortion.addListenerOrFire(this);
        TimeRefresher.register(this);
    }

    @Override
    public void abortionFired(final Abortion source, final String reason) {
        this.kill();
    }

    @Override
    public abstract void kill();
}
