package aprove.verification.dpframework.TRSProblem.Processors;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

public class ATransformationProcessor extends QTRSProcessor {

    @ParamsViaArgumentObject
    public ATransformationProcessor(final Arguments arguments) {
    }

    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        // check that we have NF(Q) sub NF(R) or Q = empty (currently we do not drop Q for other cases)
        if (qtrs.QsupersetOfLhsR() || qtrs.getQ().isEmpty()) {
            // check that we make progress
            // A-Transform({c -> c}) = {c -> c}
            // can be done infinitely many times
            if (qtrs.getMaxArity() > 0) {
                // okay, we get progress
                return true;
            }
        }
        return false;
    }

    @Override
    protected Result processQTRS(final QTRSProblem qtrs, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        if (Globals.useAssertions) {
            assert(this.isQTRSApplicable(qtrs));
        }

        // This is always true, if isQTRSApplicable is true.
        final boolean complete = qtrs.QsupersetOfLhsR() || qtrs.getQ().isEmpty();

        final QTRSProblem aqtrs = qtrs.getATransformed();

        final Implication impl = complete ? YNMImplication.EQUIVALENT : YNMImplication.SOUND;

        return ResultFactory.proved(aqtrs, impl, new ATransformationProof(qtrs, aqtrs, complete));
    }

    private static class ATransformationProof extends QTRSProof {

        private final boolean complete;
        private final QTRSProblem origTrs, resultTrs;

        private ATransformationProof(
            final QTRSProblem origTrs,
            final QTRSProblem resultTrs,
            final boolean complete) {
            this.complete = complete;
            this.origTrs = origTrs;
            this.resultTrs = resultTrs;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            String res =
                "We have applied the A-Transformation "+o.cite(Citation.FROCOS05)+" to get from an applicative problem to a standard problem. ";
            if (!this.complete) {
                res += "As not all Q-normal forms are R-normal forms we had to drop Q. "
                    + "Therefore, this is an incomplete method.";
            }
            return o.export(res);
        }

    }

    public static class Arguments {
        public boolean beComplete = true; // currently unused.
    }

}