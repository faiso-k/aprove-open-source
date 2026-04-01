package aprove.verification.oldframework.Utility;

import java.util.*;

/**
 * Class which provides some stopwatch-like functions.
 * @author Martin Mertens
 * @version $Id$
 */
public class Timer {

    private double lastStartTime; //stores when the timer was started the last time
    private double accuTime; // stores all accumulated times
    private boolean active; // stores if timer is in an active state

    public Timer() {

    this.reset();

    }

    public void start() {


    if (!this.isActive()) { // else do nothing, because timer is already started
        this.lastStartTime = System.currentTimeMillis();
        this.active = true;
    }


    }

    public void stop() {

    if (this.isActive()) { // else do nothing, because timer is already stopped
        this.active = false;
        double interval = System.currentTimeMillis() - this.lastStartTime;
        this.accuTime += interval;
    }

    }

    public boolean isActive() {

    return this.active;

    }

    public double getDuration() {

    if (!this.isActive()) {
        return this.accuTime;
    } else {
        return 0.0;
    }

    }

    public String getSmartStringDuration() {

    Calendar cal = Calendar.getInstance(TimeZone.getTimeZone("UTC"));
    cal.setTimeInMillis((long)this.accuTime);

    int days = cal.get(Calendar.DAY_OF_YEAR)-1;
    int hours = cal.get(Calendar.HOUR);
    int minutes = cal.get(Calendar.MINUTE);
    int seconds = cal.get(Calendar.SECOND);
    int millis = cal.get(Calendar.MILLISECOND);

        String tmp ="";

    if (days > 0) {
        tmp += days+" day"+Timer.ending(days)+" (!), ";
    }
    if (hours > 0) {
        tmp += hours+" hour"+Timer.ending(hours)+", ";
    };
    if (minutes > 0) {
        tmp += minutes+ " minute"+Timer.ending(minutes)+" and ";
    }

    tmp += seconds+"."+millis+" seconds";

    return tmp;

    }

    public void reset() {

    this.lastStartTime = 0.0;
    this.accuTime = 0.0;
    this.active = false;

    }

    /**
     * Generate right noun ending for singular and plural.
     */
    private static final String ending(int i) {

    switch (i) {

    case 0:   return "s";
    case 1:   return "" ;
    default:  return "s";

    }

    }



}
