/*
 * Created on Jul 3, 2006
 */
package aprove.verification.dpframework.DPProblem.Processors;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Creates a QDPProblem out of the given EDPProblem, iff the set of
 * Equations E and eSharp are empty.
 *
 * @author stein
 * @version $Id$
 */

@NoParams
public class EDPToQDPProblemProcessor extends EDPProblemProcessor {

    @Override
    protected Result processEDPProblem(EDPProblem edp, Abortion aborter) throws AbortionException {
        if (Globals.useAssertions) {
            assert(this.isEDPApplicable(edp));
        }

        QTRSProblem qtrs = QTRSProblem.create(edp.getR());
        QDPProblem qdp = QDPProblem.create(edp.getP(), qtrs, edp.getMinimal());

        Result result = ResultFactory.proved(qdp, YNMImplication.EQUIVALENT, new EDPProblemToQDPProblemProof());
        return result;
    }

    @Override
    public boolean isEDPApplicable(EDPProblem edp) {
        //applicable iff E and eSharp of the EDPProblem are both empty
        return edp.getE().isEmpty() && edp.getESharp().isEmpty();
    }


    private static class EDPProblemToQDPProblemProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            String res;
            res = "The EDP problem does not contain equations anymore, so we" +
                    " can transform it with the EDP to QDP problem processor "+o.cite(Citation.DA_STEIN)+
                        " into a QDP problem.";
            return o.export(res);
        }

    }

}
