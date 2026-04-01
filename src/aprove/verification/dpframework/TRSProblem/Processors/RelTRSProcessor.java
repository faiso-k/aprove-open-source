package aprove.verification.dpframework.TRSProblem.Processors;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

/**
 * Abstract superclass for processors operating on relative termination problems
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public abstract class RelTRSProcessor extends ProcessorSkeleton {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (obl instanceof RelTRSProblem) && this.isRelTRSApplicable((RelTRSProblem) obl);
    }

    public boolean isRelTRSApplicable(RelTRSProblem obl) {
        return true;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode,
            Abortion aborter, RuntimeInformation rti) throws AbortionException {

        RelTRSProblem problem = (RelTRSProblem)obl;
        if (problem.getR().isEmpty()) {
            return ResultFactory.proved(new RIsEmptyProof());
        }
        return this.processRelTRS(problem, aborter, rti);
    }

    abstract protected Result processRelTRS(RelTRSProblem problem, Abortion aborter, RuntimeInformation rti) throws AbortionException;


    public static class RIsEmptyProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.export("The TRS R is empty. Hence, termination is trivially proven.");
        }

        @Override
        public Element toDOM(Document doc, XMLMetaData xmlMetaData) {
            /* I don't consider the storage here, because nothing has changed
             * and I don't need any information out of this proof
             */
            return XMLTag.REL_R_IS_EMPTY_PROOF.createElement(doc);
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            return CPFTag.RELATIVE_TERMINATION_PROOF.create(doc,
                    CPFTag.R_IS_EMPTY.create(doc));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }

    }
}
