package aprove.strategies.ExecutableStrategies;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.UserStrategies.*;

public class ExecTimer extends ExecSimple implements ClockListener {

    public ExecTimer(UserStrategy str, long maxMillis, BasicObligationNode pos, RuntimeInformation rti) {
        this(str, new Clock(maxMillis, null), pos, rti);
    }

    private ExecTimer(UserStrategy str, Clock clock, BasicObligationNode pos, RuntimeInformation rti) {
        super("ETimer", str, pos, rti.copyAddClock(clock));
        clock.setListener(this);
    }

    @Override
    public void ring(Clock source) {
        this.asyncStop("Timer expired");
    }
}
