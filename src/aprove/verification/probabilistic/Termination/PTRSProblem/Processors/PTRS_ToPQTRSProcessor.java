package aprove.verification.probabilistic.Termination.PTRSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import immutables.*;

/**
 * Processor that adds the Q-Set to the PTRS Problem
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class PTRS_ToPQTRSProcessor extends PTRS_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isPTRSApplicable(final PTRSProblem obl) {
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result processPTRSProblem(final PTRSProblem ptrs, final Abortion aborter)
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

        final PQTRSProblem qtrs = PQTRSProblem.create(PR, Q, qStrat, ptrs.getTarget(), ptrs.isBasic());

        final PTRStoPQTRSProof proof = new PTRStoPQTRSProof(Q);

        return ResultFactory.proved(qtrs, YNMImplication.EQUIVALENT, proof);
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class PTRStoPQTRSProof extends Proof.DefaultProof {

        private Set<TRSFunctionApplication> Q;

        private PTRStoPQTRSProof(final Set<TRSFunctionApplication> Q) {
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
