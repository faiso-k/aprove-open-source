package aprove.verification.complexity.CpxTypedWeightedCompleteTrsProblem.Processors;

import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Algorithms.*;
import aprove.verification.complexity.CpxTypedWeightedCompleteTrsProblem.*;
import aprove.verification.complexity.CpxTypedWeightedTrsProblem.*;
import aprove.verification.complexity.CpxWeightedTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;


/**
 * Applies one narrowing step (of every inner basic term of the rhs) to all rules.
 * @author mnaaf
 */
public class CpxTypedWeightedCompleteTrsNarrowingProcessor extends CpxTypedWeightedCompleteTrsProcessor {

    @Override
    protected boolean isCpxTypedWeightedCompleteTrsApplicable(CpxTypedWeightedCompleteTrsProblem obl) {
        return true;
    }

    @Override
    protected Result processCpxTypedWeightedCompleteTrs(CpxTypedWeightedCompleteTrsProblem completeTrs, Abortion aborter) throws AbortionException {
        CpxTypedWeightedTrsProblem cpxTrs = completeTrs.getTypedWeightedTrs();

        Set<WeightedRule> newRules = TrsNarrowing.narrowRules(cpxTrs.getRules(), cpxTrs.getRules(), cpxTrs.getDefinedSymbols());

        CpxTypedWeightedTrsProblem cpxRes = CpxTypedWeightedTrsProblem.create(ImmutableCreator.create(newRules), cpxTrs.getSignature(), cpxTrs.cloneTypes(), cpxTrs.isInnermost());
        CpxTypedWeightedCompleteTrsProblem completeRes = new CpxTypedWeightedCompleteTrsProblem(cpxRes,completeTrs.allowsPartialDerivations());

        return ResultFactory.proved(completeRes, BothBounds.create(), new NarrowingProof());
    }

    private static class NarrowingProof extends CpxProof {
        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder s = new StringBuilder();
            s.append("Narrowed the inner basic terms of all right-hand sides by a single narrowing step.");
            return s.toString();
        }
    }
}
