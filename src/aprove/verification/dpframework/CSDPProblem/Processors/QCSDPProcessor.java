package aprove.verification.dpframework.CSDPProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.CSDPProblem.*;
import aprove.verification.oldframework.Utility.*;

public abstract class QCSDPProcessor extends Processor.ProcessorSkeleton {

    private static class PIsEmptyProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            final StringBuilder s = new StringBuilder();

            s.append(o.export("The TRS ") + o.math("P")
                    + o.export(" is empty. Hence, there is no ")
                    + o.math("(P,Q,R," + o.mu() + ")") + o.export("-chain."));

            return s.toString();
        }

    }

    private static final Proof pIsEmptyProof = new PIsEmptyProof();

    @Override
    public Result process(final BasicObligation obl, final BasicObligationNode oblNode,
            final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        final QCSDPProblem problem = (QCSDPProblem) obl;

        // every QCSDP processor is a "P is empty" processor, too
        // disclaimer: QDPProblemProcessor did it too
        if (problem.getDp().isEmpty()) {
            return ResultFactory.proved(QCSDPProcessor.pIsEmptyProof);
        }

        return this.processQCSDP(problem, aborter);
    }

    protected abstract Result processQCSDP(QCSDPProblem problem,
            Abortion aborter) throws AbortionException;

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        if (obl instanceof QCSDPProblem) {
            return this.isQCSDPApplicable((QCSDPProblem) obl);
        }
        return false;
    }

    public abstract boolean isQCSDPApplicable(QCSDPProblem obl);
}
