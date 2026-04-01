/*
 * Created on 13.04.2005
 */
package aprove.verification.dpframework.DPProblem.Processors;

import org.w3c.dom.*;

import aprove.cli.ObligationCache.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import aprove.xml.*;

public abstract class QDPProblemProcessor extends Processor.ProcessorSkeleton {

    /**
     * Process a QTRS with a non-empty set of rules R
     * @return
     */
    protected abstract Result processQDPProblem(QDPProblem qdp, Abortion aborter) throws AbortionException;


    @Override
    public Result process(final BasicObligation o, final BasicObligationNode oblNode, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        final QDPProblem problem = (QDPProblem) o; // this cast will succeed (see isApplicable)
        if (problem.getP().isEmpty()) {
            return ResultFactory.proved(QDPProblemProcessor.pIsEmptyProof);
        }
        if (BasicObligationCache.oblCache != null) {
            final YNM value = (YNM) BasicObligationCache.oblCache.lookup(problem);
            if (value != null) {
                switch (value) {
                case YES:
                    return ResultFactory.proved(QDPProblemProcessor.pIsCachedProof);
                case NO:
                    return ResultFactory.disproved(QDPProblemProcessor.pIsCachedProof);
                }
            }
            oblNode.addTruthValueListener(new BasicObligationCache.CacheTruthValueListener(BasicObligationCache.oblCache, o));
        }
        return this.processQDPProblem(problem, aborter);
    }

    @Override
    public boolean isApplicable(final BasicObligation o) {
        if (o instanceof QDPProblem) {
            return this.isQDPApplicable((QDPProblem) o);
        }
        return false;
    }

    public abstract boolean isQDPApplicable(QDPProblem qdp);

    final static QDPProof pIsEmptyProof = new PisEmptyProof();

    private static final class PisEmptyProof extends QDPProof {

        @Override
        public String export(final Export_Util o, VerbosityLevel level) {
            return o.export("The TRS P is empty. Hence, there is no (P,Q,R) chain.");
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            return CPFTag.DP_PROOF.create(doc,
                    CPFTag.P_IS_EMPTY.create(doc));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }


    }

    private final static Proof pIsCachedProof = new PisCachedProof();

    private static final class PisCachedProof extends Proof {

        @Override
        public String export(final Export_Util o) {
            return o.export("This QDP problem has been analyzed before.");
        }

        public String toBibTeX() {
            return "";
        }

    }

}
