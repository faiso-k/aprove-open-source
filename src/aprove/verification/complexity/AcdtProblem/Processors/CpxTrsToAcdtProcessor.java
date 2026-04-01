package aprove.verification.complexity.AcdtProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.AcdtProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.CpxTrsProblem.Processors.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

public class CpxTrsToAcdtProcessor extends RuntimeComplexityTrsProcessor {

    @Override
    protected boolean isRuntimeComplexityTrsApplicable(RuntimeComplexityTrsProblem obl) {
        return obl.getRewriteStrategy() == RewriteStrategy.INNERMOST;
    }

    @Override
    protected Result processRuntimeComplexityTrs(RuntimeComplexityTrsProblem cpxTrs, Abortion aborter)
            throws AbortionException {
        AcdtProblem cdtp = AcdtProblem.create(cpxTrs.getR());
        return ResultFactory.proved(cdtp, BothBounds.create(), new QtrsToCdtProof());
    }

    public class QtrsToCdtProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            // FIXME real proof
            return "Converted QTRS to CDT";
        }

    }

}
