package aprove.verification.complexity.LowerBounds;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Given a pair of an obligation and a lower bound (which has been inferred for the obligation previously),
 * this processor just returns the lower bound.
 *
 * This bypasses a restriction of AProVE's framework: The result of a processor cannot represent "I inferred the lower
 * bound b, but we should analyze the following obligations to improve it: obl1, obl2, ...". Instead, a processor can
 * now return an obligation of type {@code ProvenLowerBound} as obl0, which is unwrapped by this processor afterwards.
 */
public class LowerBoundPropagationProcessor extends ProcessorSkeleton {

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) {
        ComplexityValue bound = ((ProvenLowerBound) obl).getBound();
        TruthValue tv = ComplexityYNM.createLower(bound);
        return ResultFactory.provedWithValue(tv, new LowerBoundPropagationProof());
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return Options.certifier.isNone() && obl instanceof ProvenLowerBound;
    }

    public static class LowerBoundPropagationProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "Propagated lower bound.";
        }

    }

}
