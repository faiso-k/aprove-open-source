package aprove.verification.dpframework.TRSProblem.Processors;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

/**
 * Checks if the TRS S is empty. If yes, consider termination of R because it is
 * equivalent to termination of R/S.
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
@NoParams
public class RelTRSEmptinessCheckProcessor extends RelTRSProcessor {

    @Override
    public Result processRelTRS(final RelTRSProblem problem, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {

        if (problem.getS().isEmpty()) {
            return ResultFactory.proved(QTRSProblem.create(problem.getR()),
                    YNMImplication.EQUIVALENT, new SIsEmptyProof());
        } else {
            return ResultFactory.unsuccessful();
        }
    }


    public static class SIsEmptyProof extends RelTRSProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return o.export("The TRS S is empty. Hence, termination of R/S is equivalent to termination of R.");
        }

        @Override
        public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
            return XMLTag.RELTRS_EMPTY_S_PROOF.createElement(doc);
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            if (modus.isPositive()) {
                return CPFTag.RELATIVE_TERMINATION_PROOF.create(doc, CPFTag.S_IS_EMPTY.create(doc, childrenProofs[0]));
            } else {
                return CPFTag.RELATIVE_NONTERMINATION_PROOF.create(doc, childrenProofs[0]);
            }
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }

    }
}
