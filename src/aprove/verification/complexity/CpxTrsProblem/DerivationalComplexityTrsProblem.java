package aprove.verification.complexity.CpxTrsProblem;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.dpframework.BasicStructures.*;
import immutables.*;

public class DerivationalComplexityTrsProblem extends DerivationalComplexityRelTrsProblem {

    private DerivationalComplexityTrsProblem(
            ImmutableSet<Rule> R,
            RewriteStrategy rewriteStrategy) {
        super("DCpxTrs", "Derivational Complexity TRS", R, ImmutableCreator.create(Collections.emptySet()), rewriteStrategy, true);
    }

    public static DerivationalComplexityTrsProblem create(final ImmutableSet<Rule> R, final RewriteStrategy rewriteStrategy) {
        return new DerivationalComplexityTrsProblem(R, rewriteStrategy);
    }

    @Override
    public String getStrategyName() {
        return "derivationalcomplexity";
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new ComplexityProofPurposeDescriptor(this,
                "Derivational Complexity (" + this.getRewriteStrategy().getRepresentation() + ')');
    }

    @Override
    public boolean isDerivational() {
        return true;
    }

}
