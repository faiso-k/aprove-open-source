package aprove.verification.dpframework.CSDPProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.CSDPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

@NoParams
public class CSRToQCSDPProblem extends CSRProcessor {

    @Override
    public boolean isCSRApplicable(final CSRProblem csr) {
        if (Options.certifier.isCeta()) {
            return false;
        }
        return true;
    }

    @Override
    protected Result processCSR(final CSRProblem csr, final Abortion aborter)
            throws AbortionException {
        aborter.checkAbortion();

        final QCSDPProblem todo = QCSDPProblem.create(csr, true);

        final Proof proof = new CSDependencyPairsProof();
        return ResultFactory.proved(todo, YNMImplication.EQUIVALENT, proof);
    }

    private class CSDependencyPairsProof extends DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Using Improved CS-DPs " + o.cite(Citation.LPAR08)
                    + " we result in the following initial Q-CSDP problem.";
        }

    }
}
