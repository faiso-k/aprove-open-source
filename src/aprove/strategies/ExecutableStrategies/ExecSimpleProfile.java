package aprove.strategies.ExecutableStrategies;

import java.io.*;

import aprove.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.oldframework.Utility.Profiling.*;

/**
 * A simple ExecutableStrategy that replicates Executor's logging
 * for arbitrary strategy elements.
 *
 * Used by VariableStrategy in profiling mode to profile all strategy subroutines.
 */
public class ExecSimpleProfile extends ExecSimple {

    private final Clock clock;
    private final long startTime;
    private final String name;
    private BasicObligationNode pos;

    public ExecSimpleProfile(String name, UserStrategy str, BasicObligationNode pos, RuntimeInformation rti) {
        // To ensure we count only CPU time on stuff started by us, start our own clock.
        this(name, str, pos, new Clock(), rti);
    }

    private ExecSimpleProfile(String name, UserStrategy str, BasicObligationNode pos,
            Clock clock, RuntimeInformation rti) {
        super("ESProf[" + name + "]", str, pos, rti.copyAddClock(clock));
        // use this to ensure that Globals.startUpTime is initialized
        Globals.init();
        this.clock = clock;
        this.startTime = System.currentTimeMillis();
        this.name = name;
        this.pos  = pos;
    }

    @Override
    ExecutableStrategy exec() {
        if (this.exStr.isNormal()) {
            this.logProfileResult("");
        }

        return super.exec();
    }

    private void logProfileResult(String extraInfo) {
        Writer wr;
        try {
            wr = Profiling.getWriter();
            synchronized (wr) {
                Executor.logProfile(Globals.PROFILE_PREFIX_STRATEGY, this.pos, this.name,
                    extraInfo, this.startTime, this.clock.getMillisUsed(), this.exStr, wr);
            }
        } catch (IOException e) {
            System.err.println("Could not open \"profiling\" Writer");
        }
    }

    @Override
    void stop(String reason) {
        super.stop(reason);
        this.logProfileResult("<Stopped ("+reason+")>");
    }
}
