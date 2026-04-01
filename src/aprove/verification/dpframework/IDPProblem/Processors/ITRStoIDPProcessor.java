/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

@NoParams
public class ITRStoIDPProcessor extends ITRSProcessor {

    @Override
    public boolean isITRSApplicable(ITRSProblem itrs) {
        return true;
    }

    @Override
    protected Result processITRSProblem(ITRSProblem itrs, Abortion aborter)
            throws AbortionException {
        // FIXME: minimal = true?
        return ResultFactory.proved(IDPProblem.create(itrs, true, aborter), YNMImplication.EQUIVALENT, new ITRStoIDPProof());
    }

    public class ITRStoIDPProof extends DefaultProof {
        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            // FIXME: Make a real proof?
            return "Added dependency pairs";
        }
    }


}
