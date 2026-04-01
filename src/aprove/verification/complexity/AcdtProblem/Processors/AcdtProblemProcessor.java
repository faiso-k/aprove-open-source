package aprove.verification.complexity.AcdtProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.AcdtProblem.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Utility.*;

public abstract class AcdtProblemProcessor extends ProcessorSkeleton {

    private static final Proof tIsEmptyProof = new TIsEmptyProof();

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof AcdtProblem) {
            return this.isCdtApplicable((AcdtProblem) obl);
        }
        return false;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode,
            Abortion aborter, RuntimeInformation rti) throws AbortionException {
        AcdtProblem cdtProblem = (AcdtProblem) obl;
        if (cdtProblem.getTuples().isEmpty()) {
            return ResultFactory.provedWithValue(
                    ComplexityYNM.create(ComplexityValue.constant(), ComplexityValue.constant()),
                    tIsEmptyProof);
        }
        return this.processCdt(cdtProblem, aborter);
    }

    protected abstract boolean isCdtApplicable(AcdtProblem obl);

    protected abstract Result processCdt(AcdtProblem cdtProblem,
            Abortion aborter) throws AbortionException;

    private static class TIsEmptyProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("The set of dependency tuples is empty");
        }

    }
}
