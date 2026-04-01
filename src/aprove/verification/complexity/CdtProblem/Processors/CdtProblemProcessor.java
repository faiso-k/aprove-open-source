package aprove.verification.complexity.CdtProblem.Processors;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

public abstract class CdtProblemProcessor extends ProcessorSkeleton {

    private static final Proof tIsEmptyProof = new SIsEmptyProof();

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        if (obl instanceof CdtProblem) {
            return this.isCdtApplicable((CdtProblem) obl);
        }
        return false;
    }

    @Override
    public Result process(final BasicObligation obl, final BasicObligationNode oblNode,
            final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        final CdtProblem cdtProblem = (CdtProblem) obl;
        if (cdtProblem.getS().isEmpty()) {
            return ResultFactory.provedWithValueAndImplication(
                    ComplexityYNM.create(ComplexityValue.constant(), ComplexityValue.constant()),
                    BothBounds.create(),
                    CdtProblemProcessor.tIsEmptyProof);
        }
        return this.processCdt(cdtProblem, aborter);
    }

    protected abstract boolean isCdtApplicable(CdtProblem obl);

    protected abstract Result processCdt(CdtProblem cdtProblem,
            Abortion aborter) throws AbortionException;

    private static class SIsEmptyProof extends CpxProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return o.escape("The set S is empty");
        }

        @Override
        public final Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            return CPFTag.COMPLEXITY_PROOF.create(doc, CPFTag.R_IS_EMPTY.create(doc));
        }

        @Override
        public XMLMetaData adaptMetaData(final XMLMetaData metaData) {
            return metaData;
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }

    }
}
