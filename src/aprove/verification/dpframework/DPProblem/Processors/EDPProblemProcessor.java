/*
 * Created on Jan 26, 2006
 */
package aprove.verification.dpframework.DPProblem.Processors;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

/**
 * @author stein
 * @version $Id$
 */

public abstract class EDPProblemProcessor extends Processor.ProcessorSkeleton {

    /**
     * Process a ETRS with a non-empty set of rules R
     * @return
     */
    protected abstract Result processEDPProblem(EDPProblem edp, Abortion aborter) throws AbortionException;


    @Override
    public Result process(BasicObligation o, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        EDPProblem problem = (EDPProblem) o; // this cast will succeed (see isApplicable)
        if (problem.getP().isEmpty()) {
            return ResultFactory.proved(EDPProblemProcessor.pIsEmptyProof);
        } else {
            return this.processEDPProblem(problem, aborter);
        }
    }

    @Override
    public boolean isApplicable(BasicObligation o) {
        if (o instanceof EDPProblem) {
            return this.isEDPApplicable((EDPProblem) o);
        }
        return false;
    }

    public abstract boolean isEDPApplicable(EDPProblem edp);

    private final static EDPProof pIsEmptyProof = new PisEmptyProof();

    private static final class PisEmptyProof extends EDPProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.export("The TRS P is empty. Hence, there is no (P,E#,R,E) chain.");
        }

        public String toBibTeX() {
            return "";
        }
        
        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            return CPFTag.AC_DP_PROOF.create(doc,
                    CPFTag.AC_P_IS_EMPTY.create(doc));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }


    }

}
