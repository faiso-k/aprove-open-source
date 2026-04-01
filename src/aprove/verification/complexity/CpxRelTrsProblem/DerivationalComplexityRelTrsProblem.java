package aprove.verification.complexity.CpxRelTrsProblem;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import immutables.*;

public class DerivationalComplexityRelTrsProblem extends CpxRelTrsProblem {

    protected DerivationalComplexityRelTrsProblem(String shortname,
            String longname,
            final ImmutableSet<Rule> R,
            final ImmutableSet<Rule> S,
            final RewriteStrategy rewriteStrategy,
            boolean STerminatesInnermost) {
        super(shortname, longname, R, S, rewriteStrategy, STerminatesInnermost);
    }

    private DerivationalComplexityRelTrsProblem(ImmutableSet<Rule> R,
            ImmutableSet<Rule> S,
            RewriteStrategy rewriteStrategy,
            boolean STerminatesInnermost) {
        super("DCpxRelTrs", "Derivational Complexity RelTRS", R, S, rewriteStrategy, STerminatesInnermost);
    }

    public static DerivationalComplexityRelTrsProblem create(final ImmutableSet<Rule> R,
            final ImmutableSet<Rule> S,
            final RewriteStrategy rewriteStrategy,
            boolean STerminatesInnermost) {
        return new DerivationalComplexityRelTrsProblem(R, S, rewriteStrategy, STerminatesInnermost);
    }

    @Override
    public String getStrategyName() {
        return "derivationalcomplexity";
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new ComplexityProofPurposeDescriptor(this, "Derivational Runtime Complexity ("
            + this.getRewriteStrategy().getRepresentation() + ')');
    }

    @Override
    public boolean isDerivational() {
        return true;
    }

    @Override
    public BasicObligation withRules(Set<Rule> R, Set<Rule> S) {
        return new DerivationalComplexityRelTrsProblem(ImmutableCreator.create(R), ImmutableCreator.create(S), this.getRewriteStrategy(), STerminatesInnermost());
    }

    @Override
    public BasicObligation provedTerminationOfS() {
        return new DerivationalComplexityRelTrsProblem(ImmutableCreator.create(R), ImmutableCreator.create(S), this.getRewriteStrategy(), true);
    }

}
