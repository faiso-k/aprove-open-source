package aprove.verification.probabilistic.Termination.ADPProblem.AST.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.Termination.ADPProblem.AST.*;
import immutables.*;

/**
 * Probability Removal Processor as described in FLOPS24, JPK60, and journal version of FLOPS24 for ADPs
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class ADP_AST_ProbabilityRemovalProcessor extends ADP_AST_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isAST_ADPApplicable(final ADP_AST_Problem pqdp) {
        return pqdp.isNonProbabilistic();
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processAST_ADPProblem(final ADP_AST_Problem origPqdp, final Abortion aborter) throws AbortionException {
        final QTRSProblem newQtrs = origPqdp.getSwithQ().getNonProbAbstraction();

        origPqdp.getP();
        final Set<Rule> depPairs = origPqdp.getNonProbDPs();
        final QDPProblem newqdp = QDPProblem.create(ImmutableCreator.create(depPairs), newQtrs, true);

        final AST_ADPProbabilityRemovalProof NPPproof = new AST_ADPProbabilityRemovalProof(origPqdp.isInnermost());

        if (origPqdp.isBasic()) { /**BASIC**/
            return ResultFactory.proved(newqdp, YNMImplication.SOUND, NPPproof);
        } else { /**FULL and INNERMOST**/
            return ResultFactory.proved(newqdp, YNMImplication.EQUIVALENT, NPPproof);
        }
    }

    // ================================================================================
    // Proof
    // ================================================================================

    private static class AST_ADPProbabilityRemovalProof extends ADP_AST_Proof {

        private final boolean innermost;

        private AST_ADPProbabilityRemovalProof(final boolean innermost) {
            this.innermost = innermost;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            res.append(o.paragraph());
            if (this.innermost) {
                res.append("We use the probability removal processor ").append(o.cite(Citation.FLOPS24)).append(".");
            } else { //full AST
                res.append("We use the probability removal processor ").append(" (!PROTOTYPE!) ").append(".");
            }
            res.append(o.linebreak());
            res.append("As all rules have a trivial probability (1:r), we can transform it into a non-probabilistic DP problem");

            return o.export(res.toString());
        }

    }

    public static class Arguments {

        public boolean beComplete = true;
        public boolean useApplicativeCeRules = true;
    }
}
