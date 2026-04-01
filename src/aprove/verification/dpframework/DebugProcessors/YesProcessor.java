package aprove.verification.dpframework.DebugProcessors;

import aprove.*;
import aprove.Globals.AproveVersion;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * Takes a QTRS problem and says YES.
 * May be useful for debugging.
 * May be very useless in termination analysis.
 *
 * @author Andreas Kelle-Emden
 * @version $Id$
 */
@NoParams
public class YesProcessor extends Processor.ProcessorSkeleton {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (Globals.aproveVersion == AproveVersion.DEVELOPER_VERSION);
    }


    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {

        return ResultFactory.proved(new YesProof());
    }

    private static class YesProof extends Proof {

        @Override
        public String export(Export_Util o) {
            return "Always YES";
        }

    }
}
