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
 * Print nano time to stdout when called.
 *
 * @author Andreas Kelle-Emden
 * @version $Id$
 */
public class PrintTimeProcessor extends Processor.ProcessorSkeleton {

    private final String name;

    protected static long lastCall = -1;

    @ParamsViaArguments("name")
    public PrintTimeProcessor(String name) {
        this.name = name;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (Globals.aproveVersion == AproveVersion.DEVELOPER_VERSION);
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        long diff = -1;
        if (PrintTimeProcessor.lastCall >= 0) {
            long now = System.nanoTime();
            diff = now - PrintTimeProcessor.lastCall;
            PrintTimeProcessor.lastCall = now;
            System.err.println(now + " PRINT TIME <" + this.name + ">, diff: "+diff);
        } else {
            PrintTimeProcessor.lastCall = System.nanoTime();
            System.err.println(PrintTimeProcessor.lastCall + " PRINT TIME <" + this.name + ">");
        }
        return ResultFactory.proved(oblNode.getBasicObligation(), YNMImplication.EQUIVALENT, new PrintTimeProof(PrintTimeProcessor.lastCall, diff));
    }

    private static class PrintTimeProof extends Proof {

        protected long now;
        protected long diff;

        public PrintTimeProof(long now, long diff) {
            this.now  = now;
            this.diff = diff;
        }

        @Override
        public String export(Export_Util o) {
            return "Nothing done at " + this.now + ", diff: "+ this.diff;
        }

    }
}
