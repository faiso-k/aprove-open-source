package aprove.verification.complexity.CpxIntTrsProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Abstract processor class for working with {@link CpxIntTrsProblem}s.
 */
abstract public class CpxIntTrsProcessor extends ProcessorSkeleton {

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        CpxIntTrsProblem cint = (CpxIntTrsProblem) obl;
        if (cint.isSolved()) {
            return ResultFactory.provedWithValue(
                ComplexityYNM.create(ComplexityValue.constant(), ComplexityValue.constant()),
                sIsEmptyProof);
        }
        return this.processCpxIntTrs(cint, oblNode, aborter, rti);
    }

    /**
     * @param obl
     * @param oblNode
     * @param aborter
     * @param rti
     * @return
     * @throws AbortionException
     */
    abstract public Result processCpxIntTrs(
        CpxIntTrsProblem obl,
        BasicObligationNode oblNode,
        Abortion aborter,
        RuntimeInformation rti) throws AbortionException;

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        if (!(obl instanceof CpxIntTrsProblem)) {
            return false;
        }
        return this.isCpxIntTrsApplicable((CpxIntTrsProblem) obl);
    }

    /**
     * @param obl
     * @return If the processor is applicable for {@code obl}.
     */
    abstract boolean isCpxIntTrsApplicable(CpxIntTrsProblem obl);

    private static final Proof sIsEmptyProof = new SIsEmptyProof();

    private static class SIsEmptyProof extends Proof.DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return o.escape("The set S is empty");
        }

    }
}
