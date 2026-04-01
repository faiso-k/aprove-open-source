/*
 * Created on 13.04.2005
 */
package aprove.verification.dpframework.TRSProblem.Processors;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

public abstract class QTRSProcessor extends Processor.ProcessorSkeleton {



    /**
     * Process a QTRS with a non-empty set of rules R
     * @return
     */
    protected abstract Result processQTRS(QTRSProblem qtrs, Abortion aborter, RuntimeInformation rti) throws AbortionException;


    @Override
    public Result process(final BasicObligation o, final BasicObligationNode oblNode, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        final QTRSProblem problem = (QTRSProblem) o; // this cast will succeed (see isApplicable)
        if (problem.getR().isEmpty()) {
            return ResultFactory.proved(QTRSProcessor.rIsEmptyProof);
        } else {
            return this.processQTRS(problem, aborter, rti);
        }
    }

    @Override
    public boolean isApplicable(final BasicObligation o) {
        if (o instanceof QTRSProblem) {
            return this.isQTRSApplicable((QTRSProblem) o);
        }
        return false;
    }

    public abstract boolean isQTRSApplicable(QTRSProblem qtrs);

    protected final static QTRSProof rIsEmptyProof = new RisEmptyProof();

    private static final class RisEmptyProof extends QTRSProof {

        @Override
        public String export(final Export_Util o, VerbosityLevel level) {
            return o.export("The TRS R is empty. Hence, termination is trivially proven.");
        }


        public String toBibTeX() {
            return "";
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            return CPFTag.TRS_TERMINATION_PROOF.create(doc,
                    CPFTag.R_IS_EMPTY.create(doc));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }


    }

}
