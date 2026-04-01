package aprove.verification.dpframework.TRSProblem.Processors;


import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

@NoParams
public class CSRInnermostProcessor extends CSRProcessor {

    @Override
    protected Result processCSR(final CSRProblem csr, final Abortion aborter) throws AbortionException {

        if (csr.isOrthogonal(aborter)) {
            final CSRProblem newCsr = CSRProblem.createInnermost(csr);
            return ResultFactory.proved(newCsr, YNMImplication.EQUIVALENT, CSRInnermostProcessor.CSRInnermostProof);
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    @Override
    public boolean isCSRApplicable(final CSRProblem csr) {
        if (Options.certifier.isCeta()) {
            return false;
        }
        return !csr.getInnermost();
    }

    private static CSRProof CSRInnermostProof = new CSRInnermostProof();

    private static class CSRInnermostProof extends CSRProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return o.export("The CSR is orthogonal. By "+o.cite(Citation.CS_Inn)+" we can switch to innermost.");
        }

    };


}
