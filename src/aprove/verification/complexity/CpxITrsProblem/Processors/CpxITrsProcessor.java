package aprove.verification.complexity.CpxITrsProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxITrsProblem.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Utility.*;

public abstract class CpxITrsProcessor extends ProcessorSkeleton {

    private static final Proof rIsEmptyProof = new RIsEmptyProof();

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof CpxITrsProblem) {
            return this.isCpxITrsApplicable((CpxITrsProblem) obl);
        }
        return false;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode,
            Abortion aborter, RuntimeInformation rti) throws AbortionException {
        CpxITrsProblem icpx = (CpxITrsProblem) obl;
        if (icpx.getR().isEmpty()) {
            return ResultFactory.provedWithValue(ComplexityYNM.CONSTANT,
                    CpxITrsProcessor.rIsEmptyProof);
        }
        return this.processCpxITrs(icpx, aborter);
    }

    protected abstract boolean isCpxITrsApplicable(CpxITrsProblem obl);

    protected abstract Result processCpxITrs(CpxITrsProblem cpxITrs,
            Abortion aborter) throws AbortionException;

    private static final class RIsEmptyProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("This system has no rules, therefore it has constant runtime complexity");
        }

    }
}
