package aprove.verification.probabilistic.Complexity.PTRSProblem.Processors;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.Complexity.PTRSProblem.*;
import aprove.xml.*;

/**
 * @author J-C Kassing
 * @version $Id$
 */
public abstract class PTRS_Cpx_Processor extends ProcessorSkeleton {

    private static final Proof rIsEmptyProof = new RIsEmptyProof();

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        if (obl instanceof PTRS_Cpx_Problem) {
            return isCpxPTRSApplicable((PTRS_Cpx_Problem) obl);
        }
        return false;
    }

    @Override
    public Result process(final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException {
        final PTRS_Cpx_Problem cpx = (PTRS_Cpx_Problem) obl;
        if (cpx.getProbabilisticRules().isEmpty()) {
            return ResultFactory.provedWithValue(
                ComplexityYNM.create(
                    ComplexityValue.constant(),
                    ComplexityValue.constant()),
                PTRS_Cpx_Processor.rIsEmptyProof);
        }
        return processCpxPTRS(cpx, aborter);
    }

    protected abstract boolean isCpxPTRSApplicable(PTRS_Cpx_Problem obl);

    protected abstract Result processCpxPTRS(PTRS_Cpx_Problem cpxTrs,
        Abortion aborter) throws AbortionException;

    private static final class RIsEmptyProof extends CpxProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return o.escape("This system has no rules, therefore it has constant runtime complexity");
        }

        @Override
        public final Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            return CPFTag.COMPLEXITY_PROOF.create(doc,
                CPFTag.R_IS_EMPTY.create(doc));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }

    }
}
