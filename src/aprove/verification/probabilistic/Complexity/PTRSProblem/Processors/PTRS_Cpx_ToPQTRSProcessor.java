package aprove.verification.probabilistic.Complexity.PTRSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Complexity.PTRSProblem.*;
import immutables.*;

/**
 * Processor that adds the Q-Set to the PTRS Problem
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class PTRS_Cpx_ToPQTRSProcessor extends PTRS_Cpx_Processor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isCpxPTRSApplicable(final PTRS_Cpx_Problem obl) {
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result processCpxPTRS(final PTRS_Cpx_Problem ptrs, final Abortion aborter)
        throws AbortionException {
        final ImmutableSet<ProbabilisticRule> PR = ImmutableCreator.create(ptrs.getPR());
        final boolean innermost = ptrs.isInnermost();
        final Set<TRSFunctionApplication> Q = innermost ? CollectionUtils.getLeftHandSides(PR)
            : new HashSet<>();

        QRewriteStrategy qStrat;
        if (ptrs.getRewriteStrategy() == RewriteStrategy.PARALLEL_SIMULTANEOUS
            || ptrs.getRewriteStrategy() == RewriteStrategy.PARALLEL_SIMULTANEOUS_INNERMOST) {
            qStrat = QRewriteStrategy.Q_PARALLEL_SIMULTANEOUS;
        } else {
            qStrat = QRewriteStrategy.Q_FULL;
        }

        final PQTRS_Cpx_Problem qtrs = PQTRS_Cpx_Problem.create(PR, Q, qStrat, ptrs.isBasic());

        final CpxPTRS_ToPQTRSProof proof = new CpxPTRS_ToPQTRSProof(Q);

        return ResultFactory.proved(qtrs, BothBounds.create(), proof);
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class CpxPTRS_ToPQTRSProof extends Proof.DefaultProof {

        private Set<TRSFunctionApplication> Q;

        private CpxPTRS_ToPQTRSProof(final Set<TRSFunctionApplication> Q) {
            this.Q = Q;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuffer s = new StringBuffer();
            s.append(o.export("Transformed PTRS into PQTRS. Q is:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.Q, Export_Util.NICE_SET));
            return s.toString();
        }
    }

}
