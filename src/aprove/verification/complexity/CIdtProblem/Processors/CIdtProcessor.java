package aprove.verification.complexity.CIdtProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CIdtProblem.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Processors.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Marcel Klinzing
 */
public abstract class CIdtProcessor<MarkMetaData extends Result> extends
        IDPProcessor<Result, CIdtProblem> {

    protected CIdtProcessor(String description) {
        super(description);
    }

    @Override
    public boolean isIDPApplicable(IDPProblem idp) {
        if (idp instanceof CIdtProblem) {
            CIdtProblem cIdtProb = (CIdtProblem) idp;
            return this.isCIdtApplicable(cIdtProb);
        }

        return false;
    }

    @Override
    protected Result processIDPProblem(final CIdtProblem idt,
        final Abortion aborter) throws AbortionException {

        if (idt.getS().isEmpty()) {
            return ResultFactory.provedWithValue(
                ComplexityYNM.create(ComplexityValue.constant(), ComplexityValue.constant()),
                new SIsEmptyProof());
        }

        return this.processCIdtProblem(idt, aborter);
    }

    protected abstract Result processCIdtProblem(CIdtProblem idt, Abortion aborter)
        throws AbortionException;

    protected abstract boolean isCIdtApplicable(CIdtProblem idt);

    protected static class SIsEmptyProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("The set S is empty");
        }

    }
}
