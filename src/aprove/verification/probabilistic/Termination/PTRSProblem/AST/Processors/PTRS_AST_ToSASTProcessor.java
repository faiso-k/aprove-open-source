package aprove.verification.probabilistic.Termination.PTRSProblem.AST.Processors;

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
 * Processor that loosens the Probabilistic Termination Result
 * that we try to prove.
 * Since SAST => AST, we try to prove SAST instead of AST.
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class PTRS_AST_ToSASTProcessor extends PTRS_AST_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isPTRSApplicable(final PTRSProblem ptrs) {
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result processPTRSProblem(final PTRSProblem ptrs, final Abortion aborter)
        throws AbortionException {
        final Set<ProbabilisticRule> pr = ptrs.getProbabilisticRules();
        final RewriteStrategy strat = ptrs.getRewriteStrategy();

        final PTRSProblem newptrs = PTRSProblem.create(ImmutableCreator.create(pr), strat, ProbabilisticTerminationResult.SAST, ptrs.isBasic());

        final ASTtoPASTProof proof = new ASTtoPASTProof();

        return ResultFactory.proved(newptrs, YNMImplication.SOUND, proof);
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class ASTtoPASTProof extends Proof.DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "A PTRS R is AST if it is PAST";
        }
    }
}
