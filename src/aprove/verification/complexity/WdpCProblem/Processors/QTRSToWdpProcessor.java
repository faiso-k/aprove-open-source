package aprove.verification.complexity.WdpCProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.WdpCProblem.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.Utility.*;

public class QTRSToWdpProcessor extends QTRSProcessor {

    @Override
    public boolean isQTRSApplicable(QTRSProblem qtrs) {
        // Only empty Q or innermost
        return qtrs.getQ().isEmpty() ||qtrs.QsupersetOfLhsR();
    }

    @Override
    protected Result processQTRS(QTRSProblem qtrs, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        boolean innermost = qtrs.QsupersetOfLhsR();
        WDPProblemRC wdpProblem = WDPProblemRC.create(qtrs.getR(), innermost);
        return ResultFactory.proved(wdpProblem, BothBounds.create(), new QTRSToWdpProof());
    }

    public class QTRSToWdpProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            // FIXME real proof
            return "Converted QTRS to W(i)DP";
        }

    }

}
