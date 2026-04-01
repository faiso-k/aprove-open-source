package aprove.verification.dpframework.MCSProblem.mcnp;

import java.util.*;

/*
 * Used for hierarchy time count
 * If A runs B and then C, it allows to print time for B,C and A which equals B=C.
 */

public class Timer {

    private Stack<Long> _times = new Stack<Long>();

    private long _lastStart = System.currentTimeMillis();;

    // The event which time is sum of other events
    public void startNextSum()
    {
        this._times.push(Long.valueOf(0));
    }

    // the independent event
    public void startNext()
    {
        this._lastStart = System.currentTimeMillis();
    }

    public long endCurrent()
    {
        if (this._lastStart >= 0) {
            long timeTook = System.currentTimeMillis() - this._lastStart;
            long lastTotal = this._times.pop();
            lastTotal += timeTook;
            this._times.push(lastTotal);
            this._lastStart = -1;
            return timeTook;
        } else {
            long lastTotal = this._times.pop();
            if (!this._times.isEmpty()) {
                long lastTotalParent = this._times.pop();
                lastTotalParent += lastTotal;
                this._times.push(lastTotalParent);
            }
            return lastTotal;
        }
    }

    // ghours:minutes:seconds:miliseconds
    public static String printTime(long time) {
        String reportTime = time/(60*60*1000)+":"+(time/(60*1000))%60+":"+(time/1000)%60+":"+time % 1000;
        return reportTime;
    }
}
