/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

@NoParams
public class ITRSConstantFoldingProcessor extends ITRSProcessor {

    @Override
    public boolean isITRSApplicable(ITRSProblem itrs) {
        return true;
    }

    @Override
    protected Result processITRSProblem(ITRSProblem itrs, Abortion aborter)
            throws AbortionException {
        Set<? extends GeneralizedRule> oR = itrs.getR();
        Set<GeneralizedRule> R = new LinkedHashSet<GeneralizedRule>(oR.size());
        for (GeneralizedRule r : oR) {
            R.add(ConstantFolding.fold(r, itrs.getPredefinedMap()));
        }

        // FIXME  - noschinski: update Q?
        IQTermSet newQ = itrs.getQ();

        return ResultFactory.proved(ITRSProblem.create(R, newQ), YNMImplication.EQUIVALENT,
                new ITRSConstantFoldingProof());
    }

    public class ITRSConstantFoldingProof extends DefaultProof {
        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            // FIXME: Make a real proof?
            return "Applied constant integer rules as far as possible.";
        }
    }

}
