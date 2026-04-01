package aprove.verification.dpframework.DebugProcessors;

import aprove.*;
import aprove.Globals.AproveVersion;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;

/**
 * Takes a QTRS problem and fails.
 * May be useful for debugging.
 * May be very useless in termination analysis.
 *
 * @author Andreas Kelle-Emden
 * @version $Id$
 */
@NoParams
public class FailProcessor extends Processor.ProcessorSkeleton {

    public FailProcessor() {
        // presumably called by the Machine once per occurrence
        // of the FailProcessor in the strategy
        if (Globals.DEBUG_FUHS) {
            System.err.println("Fail processor " + this + " CREATED");
        }
    }
    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (Globals.aproveVersion == AproveVersion.DEVELOPER_VERSION);
    }


    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        // presumably called by the Machine once per call
        // of the FailProcessor when the strategy program is executed
        if (Globals.DEBUG_FUHS) {
            System.err.println("Fail processor " + this
                + " CALLED on OBLIGATION " + obl.getId());
        }
        return ResultFactory.unsuccessful();
    }

}
