package aprove.verification.complexity.CpxTypedWeightedTrsProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxTypedWeightedTrsProblem.*;
import aprove.verification.complexity.CpxWeightedTrsProblem.*;
import aprove.verification.complexity.CpxWeightedTrsProblem.Processors.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Type Inference for CpxTrs, using Complexity.Lowerbounds.
 *
 * @author mnaaf
 *
 */
public class CpxWeightedTrsTypeInferenceProcessor extends CpxWeightedTrsProcessor {

    @Override
    protected boolean isCpxWeightedTrsApplicable(CpxWeightedTrsProblem obl) {
        return true;
    }

    @Override
    protected Result processCpxWeightedTrs(CpxWeightedTrsProblem cpxTrs, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        CpxTypedWeightedTrsProblem res = TypeInference.inferTypes(cpxTrs);
        return ResultFactory.proved(res, BothBounds.create(), new TypeInferenceProof());
    }

    private class TypeInferenceProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("Infered types.");
        }
    }

}
