package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * This processor transforms the relative TRS problem (R, S) into the standard
 * (Q)TRS problem R if R is left-linear, S is right-linear and there is no
 * overlap between left sides of R and right sides of S.
 * This is due to a result of Bachmair and Dershowitz from 1986.
 * Note: QC stands for "quasi-commutativity".
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
@NoParams
public class RelTRSQCCheckProcessor extends RelTRSProcessor {

    @Override
    public Result processRelTRS(RelTRSProblem problem, Abortion aborter, RuntimeInformation rti) throws AbortionException {

        ImmutableSet<Rule> R = problem.getR();
        Set<Rule> S = problem.getS();
        Set<TRSTerm> rLhs = new LinkedHashSet<TRSTerm>(R.size());
        for (Rule rule : R) {
            if (!rule.getLeft().isLinear()) {
                return ResultFactory.notApplicable("R is not left-linear.");
            } else {
                rLhs.add(rule.getLeft());
            }
        }
        Set<TRSTerm> sRhs = new LinkedHashSet<TRSTerm>(S.size());
        for (Rule rule : S) {
            if (!rule.getRight().isLinear()) {
                return ResultFactory.notApplicable("S is not right-linear.");
            } else {
                sRhs.add(rule.getRight());
            }
        }

        if (!this.overlapping(rLhs, sRhs)) {
            BasicObligation result = QTRSProblem.create(R);
            Proof proof = new RelTRSQCCheckProof();
            return ResultFactory.proved(result, YNMImplication.EQUIVALENT, proof);
        } else {
            return ResultFactory.unsuccessful("Non-overlapping condition not met.");
        }
    }

    /**
     * Check if the two sets u and v of terms are overlapping. This is the case if there is
     * a term t1 from u and a term t2 from v such that t1 is unifiable with a non-variable
     * subterm of t2 or vice versa.
     */
    private boolean overlapping(Set<TRSTerm> u, Set<TRSTerm> v) {
        for (TRSTerm t1 : u) {
            for (TRSTerm t2 : v) {
                if (this.overlaps(t1, t2) || this.overlaps(t2, t1)) {
                    return true;
                }
            }
        }
        return false;
    }

    private boolean overlaps(TRSTerm t1, TRSTerm t2) {

        if (t2.isVariable()) {
            return false;
        }
        if (t1.isVariable()) {
            return true; // variables can be unified with all terms
        }
        Set<TRSFunctionApplication> t2Subterms = t2.getNonVariableSubTerms();
        for (TRSTerm subterm : t2Subterms) {
            if (!t1.unifiesVarDisjoint(subterm)) {
                return true;
            }
        }
        return false;
    }

    public static class RelTRSQCCheckProof extends RelTRSProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.export("There is no left-hand side in R that overlaps with a right-hand side in S. "
                    + "Therefore, according to " + o.cite(Citation.BD86) + ", R quasi-commutes over S, "
                    + "which implies that termination of R/S and R is equivalent.");
        }

    }
}
