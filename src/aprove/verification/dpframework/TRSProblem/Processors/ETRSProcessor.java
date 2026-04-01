/*
 * Created on Jan 26, 2006
 */
package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import aprove.xml.*;

/**
 * @author stein
 * @version $Id$
 */

public abstract class ETRSProcessor extends Processor.ProcessorSkeleton {

    /**
     * Process a ETRS with a non-empty set of rules R
     */
    protected abstract Result processETRS(ETRSProblem etrs, Abortion aborter) throws AbortionException;


    @Override
    public Result process(BasicObligation o, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        ETRSProblem problem = (ETRSProblem) o; // this cast will succeed (see isApplicable)
        if (problem.getR().isEmpty()) {
            return ResultFactory.proved(ETRSProcessor.rIsEmptyProof);
        } else {
            return this.processETRS(problem, aborter);
        }
    }

    @Override
    public boolean isApplicable(BasicObligation o) {
        if (o instanceof ETRSProblem) {
            return this.isETRSApplicable((ETRSProblem) o);
        }
        return false;
    }

    public abstract boolean isETRSApplicable(ETRSProblem etrs);

    private final static ETRSProof rIsEmptyProof = new RisEmptyProof();

    /**
     * @author stein
     * @version $Id$
     */
    private static final class RisEmptyProof extends ETRSProof {

        public String toBibTeX() {
            return "";
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.export("The TRS R is empty. Hence, termination is trivially proven.");
        }
        
        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            return CPFTag.AC_TERMINATION_PROOF.create(doc,
                    CPFTag.AC_R_IS_EMPTY.create(doc));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }


    }

}
