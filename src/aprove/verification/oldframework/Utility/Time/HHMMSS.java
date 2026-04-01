/*
 * Created on 23.06.2004
 */
package aprove.verification.oldframework.Utility.Time;

/**
 * @author thiemann
 * a class for easy access to hours, minutes, seconds of a timemillis value
 */

public class HHMMSS {

    public final int hh;
    public final int mm;
    public final int ss;
    public final long time;

    private static final int maxHH = Integer.MAX_VALUE;

    public HHMMSS(long time) {
        this.time = time;
        time /= 1000;
        this.ss = (int) time % 60;
        time /= 60;
        this.mm = (int) time % 60;
        time /= 60;
        if (time > HHMMSS.maxHH) {
            this.hh = HHMMSS.maxHH;
        } else {
            this.hh = (int) time;
        }
    }

    /**
     * default output of time
     */
    @Override
    public String toString() {
        String s;
        if (this.ss < 10) {
            s = this.mm+":0"+this.ss;
        } else {
            s = this.mm+":"+this.ss;
        }
        if (this.hh > 0) {
            if (this.mm < 10) {
                s = this.hh+":0"+s;
            } else {
                s = this.hh+":"+s;
            }
        }
        return s;
    }

}
