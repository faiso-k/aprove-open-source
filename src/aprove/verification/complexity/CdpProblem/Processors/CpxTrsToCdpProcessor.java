package aprove.verification.complexity.CdpProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CdpProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Creates a {@link CdpProblem} from an innermost {@link RuntimeComplexityTrsProblem}
 */
public class CpxTrsToCdpProcessor extends ProcessorSkeleton {

    @Override
    public boolean isApplicable(BasicObligation bobl) {
        return (bobl instanceof RuntimeComplexityTrsProblem)
                && ((RuntimeComplexityTrsProblem)bobl).getRewriteStrategy() != RewriteStrategy.FULL;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode,
            Abortion aborter, RuntimeInformation rti) throws AbortionException {
        RuntimeComplexityTrsProblem cpx = (RuntimeComplexityTrsProblem)obl;
        CdpProblem cdpProblem = CdpProblem.create(cpx.getR());
        /* This transformation is not complete, as we might forget that same
         * symbols are defined when creating the cdpProblem. */
        return ResultFactory.proved(cdpProblem, UpperBound.create(), new QTRSToCdpProof());
    }

    public class QTRSToCdpProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            // FIXME real proof
            return "Converted CpxTrs to CDP";
        }

    }

}
