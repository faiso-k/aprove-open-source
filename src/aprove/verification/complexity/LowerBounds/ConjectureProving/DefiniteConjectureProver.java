package aprove.verification.complexity.LowerBounds.ConjectureProving;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.InductionProof.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class DefiniteConjectureProver extends ConjectureProver {

    private TermRewriter rewriter;

    public DefiniteConjectureProver(LowerBoundsToolbox toolbox,
            TermRewriter rewriter,
            Conjecture conjecture) {
        super(conjecture, toolbox);
        this.rewriter = rewriter;
    }

    @Override
    public Set<InductionProof> execProve() throws AbortionException {
        Set<InductionProof> res = new LinkedHashSet<>();
        Set<InductionStep> inductionSteps = this.proveInductiveCase();
        for (InductionStep is : inductionSteps) {
            InductionBase ib = this.proveBaseCase();
            if (ib != null) {
                res.add(new SuccessfulInductionProof(ib, is));
            }
        }
        return res;
    }

    private Set<InductionStep> proveInductiveCase() throws AbortionException {
        Set<InductionStep> res = new LinkedHashSet<>();
        InductionHypothesis inductionHypothesis = this.buildInductionHypothesis();
        if (inductionHypothesis == null || this.isTrivial(inductionHypothesis)) {
            return null;
        }
        try {
            this.toolbox.trs.setInductionHypothesis(inductionHypothesis);
            BidirectionalMap<TRSTerm, TRSTerm> map = this.buildReplacementMapForInductiveCase();
            TRSTerm rightNorm = this.toolbox.pfHelper.normalize(this.conjecture.getRight().replaceAll(map.getLRMap()));
            Set<RewriteSequence> allLeftNormalizations = this.rewriter.normalize((TRSFunctionApplication) this.conjecture.getLeft()
                    .replaceAll(map.getLRMap()));
            for (RewriteSequence leftNormalization : allLeftNormalizations) {
                if (this.substitutionsForIHAreIncreasing(inductionHypothesis, leftNormalization, this.toolbox.pfHelper)) {
                    TRSTerm leftNorm = leftNormalization.getResult();
                    boolean successful = this.toolbox.genEqRewriter.areEquivalent(leftNorm, rightNorm);
                    if (successful) {
                        res.add(new InductionStep(leftNormalization.replaceAll(this.reverseReplacementMapForInductiveCase(map))));
                    }
                }
            }
            return res;
        } finally {
            this.toolbox.trs.removeInductionHypothesis();
        }
    }

    private boolean isTrivial(InductionHypothesis inductionHypothesis) {
        return this.toolbox.genEqRewriter.areEquivalent(inductionHypothesis.getLeft(), inductionHypothesis.getRight());
    }

    private InductionBase proveBaseCase() throws AbortionException {
        TRSSubstitution sigma = TRSSubstitution.create(this.toolbox.inductionVar, PFHelper.ZERO.getTerm());
        TRSFunctionApplication lhs = this.conjecture.getLeft().applySubstitution(sigma);
        TRSTerm rhs = this.toolbox.pfHelper.normalize(this.conjecture.getRight().applySubstitution(sigma));
        Set<RewriteSequence> allLeftNormalizations = this.rewriter.normalize(lhs);
        for (RewriteSequence leftNormalization : allLeftNormalizations) {
            TRSTerm lhsNorm = leftNormalization.getResult();
            boolean successful = this.toolbox.genEqRewriter.areEquivalent(lhsNorm, rhs);
            if (successful) {
                return new InductionBase(leftNormalization);
            }
        }
        return null;
    }
}
