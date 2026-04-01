package aprove.verification.complexity.LowerBounds.ConjectureProving;

import java.util.*;
import java.util.Map.Entry;

import aprove.strategies.Abortions.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.complexity.LowerBounds.Util.Renaming.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


public abstract class ConjectureProver {

    RenamingSession session;
    Conjecture conjecture;
    LowerBoundsToolbox toolbox;


    public ConjectureProver(Conjecture conjecture, LowerBoundsToolbox toolbox) {
        super();
        this.conjecture = conjecture;
        this.toolbox = toolbox;
        this.session = toolbox.renamingCentral.getSession();
    }

    public final Set<InductionProof> prove() {
        if (!this.conjecture.getLeft().getVariables().contains(this.toolbox.inductionVar)) {
            return Collections.emptySet();
        } else {
            return this.execProve();
        }
    }

    public abstract Set<InductionProof> execProve();

    BidirectionalMap<TRSTerm, TRSTerm> buildReplacementMapForInductiveCase() {
        BidirectionalMap<TRSTerm, TRSTerm> res = new BidirectionalMap<>();
        TRSTerm substitute =
            TRSTerm.createFunctionApplication(PFHelper.ADD, this.toolbox.inductionCons, PFHelper.ONE.getTerm());
        res.putLR(this.toolbox.inductionVar, substitute);
        return res;
    }

    Map<TRSTerm, TRSTerm> reverseReplacementMapForInductiveCase(BidirectionalMap<TRSTerm, TRSTerm> map) {
        Map<TRSTerm, TRSTerm> res = new LinkedHashMap<>();
        for (Entry<TRSTerm, TRSTerm> e: map.getRLMap().entrySet()) {
            if (e.getKey().isConstant()) {
                res.put(e.getKey(), e.getValue());
            }
        }
        res.put(this.toolbox.inductionCons, this.toolbox.inductionVar);
        return res;
    }

    InductionHypothesis buildInductionHypothesis() throws AbortionException {
        TRSSubstitution sigma = TRSSubstitution.create(this.toolbox.inductionVar, this.toolbox.inductionCons);
        TRSFunctionApplication lhs = this.conjecture.getLeft().applySubstitution(sigma);
        TRSTerm normalizedLhs = this.toolbox.pfHelper.normalize(lhs);
        if (normalizedLhs.isVariable()) {
            return null;
        }
        TRSTerm rhs = this.conjecture.getRight().applySubstitution(sigma);
        rhs = this.toolbox.pfHelper.normalize(rhs);
        return new InductionHypothesis((TRSFunctionApplication) normalizedLhs, rhs);
    }

    boolean substitutionsForIHAreIncreasing(InductionHypothesis ih, RewriteSequence seq, PFHelper pfHelper) {
        for (RewriteStep step: seq) {
            AbstractRule rule = step.getRule();
            TRSSubstitution matcher = ih.getLeft().getMatcher(rule.getLeft());
            if (matcher != null && matcher.isVariableRenaming() && ih.getRight().applySubstitution(matcher).equals(rule.getRight())) {
                TRSSubstitution sigma = step.getSigma();
                for (TRSVariable v: ih.getLeft().getVariables()) {
                    TRSTerm res = v.applySubstitution(sigma);
                    assert PFHelper.isArithExp(res);
                    TRSTerm normalizedRes = pfHelper.normalize(res);
                    if (!normalizedRes.getVariables().equals(Collections.singleton(v))) {
                        return false;
                    }
                }
            }
        }
        return true;
    }
}
