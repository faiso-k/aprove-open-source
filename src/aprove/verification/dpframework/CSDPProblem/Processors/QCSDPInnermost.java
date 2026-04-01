package aprove.verification.dpframework.CSDPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CSDPProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.theoremprover.TerminationProofs.*;

@NoParams
public class QCSDPInnermost
        extends QCSDPProcessor {

    @Override
    public boolean isQCSDPApplicable(QCSDPProblem obl) {
        if (obl.isInnermost()) {
            return false;
        }
        if (!obl.isMinimal()) {
            return false;
        }
        return true;
    }

    @Override
    protected Result processQCSDP(QCSDPProblem problem, Abortion aborter)
            throws AbortionException {
        if (Globals.useAssertions) {
            assert (!problem.isInnermost());
            assert (problem.isMinimal());
        }
        ReplacementMap rm = problem.getReplacementMap();

        // our new Q = lhs(R) is:
        Set<TRSFunctionApplication> lhsR = new LinkedHashSet<TRSFunctionApplication>();
        for (Rule l_to_r : problem.getR()) {
            lhsR.add(l_to_r.getLeft());
        }
        QTermSet newQ = new QTermSet(lhsR);

        // check that NFMu(R) \subseteq NFMu(Q)
        for (TRSTerm q : problem.getQ().getTerms()) {
            rm.inQMuNormalForm(newQ, q);
        }

        Set<Rule> rulesAndPairs = new LinkedHashSet<Rule>(problem.getR());
        rulesAndPairs.addAll(problem.getDp());
        // check that R is orthogonal (i.e. linear lhs and has no critical
        // pairs)
        for (Rule l_to_r : rulesAndPairs) {
            if (!l_to_r.getLeft().isLinear()) {
                return ResultFactory.unsuccessful();
            }
        }
        if (GeneralizedRule.getCriticalPairs(rulesAndPairs).hasNext(aborter)) {
            return ResultFactory.unsuccessful();
        }

        QCSDPProblem newProblem = QCSDPProblem.create(problem, newQ);

        // check that no lhs of R overlaps with any rule from P
        return ResultFactory.proved(newProblem, YNMImplication.EQUIVALENT,
                QCSDPInnermost.proof);
    }

    private static Proof proof = new QCSDPInnermostProof();

    private static class QCSDPInnermostProof
            extends Proof {

        @Override
        public String export(Export_Util o) {
            return o.escape("The QCSDP Problem is minimal, ")
                    + o.math("R + P")
                    + o.escape(" is orthogonal, and "
                            + "NFMu(R) \\subseteq NFMu(Q). ")
                    + o.escape(" Hence by ") + o.cite(Citation.DA_EMMES)
                    + o.export(" we can switch to innermost.");
        }
    };
}
