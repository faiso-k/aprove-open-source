package aprove.verification.complexity.CpxRntsProblem.Processors;

import java.util.LinkedHashSet;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Algorithms.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Propagates equalities from the guard into the rhs to simplify rules
 * (see EqualityPropagation for an example).
 *
 * @author mnaaf
 *
 */
public class CpxRntsSimplificationProcessor extends ProcessorSkeleton {

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        CpxRntsProblem rnts = (CpxRntsProblem) obl;

        Set<RntsRule> newRules = new LinkedHashSet<>();
        for (RntsRule rule : rnts.getRules()) {
            newRules.add(EqualityPropagation.apply(rule));
        }

        CpxRntsProblem newObl = rnts.cloneWithNewRules(ImmutableCreator.create(newRules));
        return ResultFactory.proved(newObl, BothBounds.create(), new SimplificationProof());
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (obl instanceof CpxRntsProblem);
    }

    private static class SimplificationProof extends CpxProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("Simplified the RNTS by moving equalities from the constraints into the right-hand sides.");
        }

    }

}
