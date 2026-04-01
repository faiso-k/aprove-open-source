package aprove.verification.dpframework.CSDPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CSDPProblem.*;
import immutables.*;

public class QCSDPPairNarrowingProcessor
        extends QCSDPTransformationProcessor {

    private final CapMuEstimation eCapMu;

    private final boolean increasingAllowed;

    @ParamsViaArguments({"eCapMu", "increasingAllowed"})
    public QCSDPPairNarrowingProcessor(CapMuEstimation eCapMu, boolean increasingAllowed) {
        this.eCapMu = eCapMu;
        this.increasingAllowed = increasingAllowed;
    }

    @Override
    protected TransformationInfo applyTransformation(QCSDPProblem problem,
            Rule s_to_t_orig, GeneralizedTRS r) {
        Rule s_to_t = s_to_t_orig
                .getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);

        ReplacementMap mu = problem.getReplacementMap();
        QTermSet q = problem.getQ();
        boolean innermost = problem.isInnermost();

        TRSTerm cappedT = this.eCapMu.capMu(mu, q, r, innermost, s_to_t);

        if (!s_to_t.getRight().equals(cappedT)) {
            // R rules might be applied to t
            return null;
        }

        // otherwise narrow s_to_t with every u_to_v in P
        Set<Rule> newPairs = new LinkedHashSet<Rule>();
        for (Rule u_to_v : problem.getDp()) {
            TRSSubstitution mgu = u_to_v.getLhsInStandardRepresentation().getMGU(
                    s_to_t.getRight());
            if (mgu == null) {
                continue;
            }

            TRSFunctionApplication smgu = s_to_t.getLeft().applySubstitution(mgu);
            TRSTerm vmgu = u_to_v.getRhsInStandardRepresentation().applySubstitution(mgu);
            Rule smgu_to_vmgu = Rule.create(smgu, vmgu);

            newPairs.add(smgu_to_vmgu);

            if (!this.increasingAllowed && newPairs.size() > 1) {
                return null;
            }
        }

        return new TransformationInfo(false, true, ImmutableCreator.create(newPairs));
    }

    @Override
    protected String getTransformationName() {
        return "Context-Sensitive Pair Narrowing";
    }

    @Override
    public boolean isQCSDPApplicable(QCSDPProblem obl) {
        return true;
    }

    @Override
    protected Citation[] getCitations() {
        return new Citation[] { Citation.DA_EMMES };
    }
}
