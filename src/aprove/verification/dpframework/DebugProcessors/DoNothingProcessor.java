package aprove.verification.dpframework.DebugProcessors;

import aprove.*;
import aprove.Globals.AproveVersion;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * Takes an arbitrary problem and does nothing but has success.
 * May be useful for debugging.
 * May be very useless in termination analysis.
 *
 * @author Andreas Kelle-Emden
 */
public class DoNothingProcessor extends Processor.ProcessorSkeleton {

    protected final int fibLoop;
    protected final boolean checkAbortions;
    private final int sleepTime;

    @ParamsViaArgumentObject
    public DoNothingProcessor(final Arguments arguments) {
        this.fibLoop = arguments.fibLoop;
        this.sleepTime = arguments.sleepTime;
        this.checkAbortions = arguments.checkAbortions;
    }

    /**
     * Do something very important like calculating a fibonacci number.
     * Checks for abortions if aborter is not null.
     */
    public static int fib(final int n, final Abortion aborter) throws AbortionException {
        if (n <= 0) {
            return 0;
        }
        if (n == 1) {
            if (aborter != null) {
                aborter.checkAbortion();
            }
            return 1;
        }
        return DoNothingProcessor.fib(n - 2, aborter) + DoNothingProcessor.fib(n - 1, aborter);
    }

    /**
     * Do nothing, but respect aborter.
     */
    public static void wait(final int n, final Abortion aborter) throws AbortionException {
        try {
            int todo = n;
            while (todo > 100) {
                Thread.sleep(100);
                aborter.checkAbortion();
                todo -= 100;
            }
            if (todo > 0) {
                Thread.sleep(todo);
            }
        } catch (final InterruptedException e) {
        }
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return (Globals.aproveVersion == AproveVersion.DEVELOPER_VERSION);
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        //log.info("Do Nothing started at " + System.nanoTime());
        // Do something very important
        Abortion usedAborter;
        if (this.checkAbortions) {
            usedAborter = aborter;
        } else {
            usedAborter = null;
        }

        if (this.sleepTime > 0) {
            DoNothingProcessor.wait(this.sleepTime, usedAborter);
        } else {
            DoNothingProcessor.fib(this.fibLoop, usedAborter);
        }

        //log.info("Do Nothing stopped at " + System.nanoTime());

        return ResultFactory.proved(oblNode.getBasicObligation(), YNMImplication.EQUIVALENT, new DoNothingProof());
    }

    private static class DoNothingProof extends Proof {

        @Override
        public String export(final Export_Util o) {
            return "Nothing done. But with success.";
        }

    }

    public static class Arguments {
        public int fibLoop = 0;
        public int sleepTime = 0;
        public boolean checkAbortions = true;
    }
}
