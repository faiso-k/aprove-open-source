package aprove.verification.complexity.CpxTypedWeightedTrsProblem.Processors;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxTypedWeightedTrsProblem.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

public abstract class CpxTypedWeightedTrsProcessor extends ProcessorSkeleton {

    private static final Proof rIsEmptyProof = new RIsEmptyProof();

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        if (obl instanceof CpxTypedWeightedTrsProblem) {
            return isCpxTypedWeightedTrsApplicable((CpxTypedWeightedTrsProblem) obl);
        }
        return false;
    }

    @Override
    public Result process(final BasicObligation obl, final BasicObligationNode oblNode,
            final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        final CpxTypedWeightedTrsProblem cpx = (CpxTypedWeightedTrsProblem)obl;
        if (cpx.getRules().isEmpty()) {
            return ResultFactory.provedWithValue(
                    ComplexityYNM.CONSTANT, rIsEmptyProof);
        }
        return processCpxTypedWeightedTrs(cpx, aborter);
    }

    protected abstract boolean isCpxTypedWeightedTrsApplicable(CpxTypedWeightedTrsProblem obl);

    protected abstract Result processCpxTypedWeightedTrs(CpxTypedWeightedTrsProblem cpxTrs,
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
