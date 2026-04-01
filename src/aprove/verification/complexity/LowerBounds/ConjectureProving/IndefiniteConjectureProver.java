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

public class IndefiniteConjectureProver extends ConjectureProver {

    private TermRewriter rewriter;
    private InductionBase inductionBase;

    public IndefiniteConjectureProver(LowerBoundsToolbox toolbox,
            TermRewriter rewriter,
            Conjecture conjecture) {
        super(conjecture, toolbox);
        this.toolbox = toolbox;
        this.rewriter = rewriter;
        this.conjecture = conjecture;
        TRSSubstitution sigma = TRSSubstitution.create(toolbox.inductionVar, PFHelper.ZERO.getTerm());
        TRSFunctionApplication inductionBaseStartTerm = conjecture.getLeft().applySubstitution(sigma);
        this.inductionBase = new InductionBase(new RewriteSequence(inductionBaseStartTerm, toolbox));
        this.session = toolbox.renamingCentral.getSession();
    }

    @Override
    public Set<InductionProof> execProve() throws AbortionException {
        Set<InductionProof> res = new LinkedHashSet<>();
        try {
            InductionHypothesis inductionHypothesis = this.buildInductionHypothesis();
            if (inductionHypothesis != null) {
                this.toolbox.trs.setInductionHypothesis(inductionHypothesis);
                BidirectionalMap<TRSTerm, TRSTerm> map = this.buildReplacementMapForInductiveCase();
                Set<RewriteSequence> allLeftNormalizations = this.rewriter.normalize((TRSFunctionApplication) this.conjecture.getLeft()
                        .replaceAll(map.getLRMap()));
                for (RewriteSequence leftNormalization : allLeftNormalizations) {
                    if (this.substitutionsForIHAreIncreasing(inductionHypothesis, leftNormalization, this.toolbox.pfHelper)) {
                        if (leftNormalization.applied(inductionHypothesis)) {
                            InductionStep is = new InductionStep(leftNormalization.replaceAll(this.reverseReplacementMapForInductiveCase(map)));
                            res.add(new SuccessfulInductionProof(this.inductionBase, is));
                        }
                    }
                }
            }
        } finally {
            this.toolbox.trs.removeInductionHypothesis();
        }
        return res;
    }

}
