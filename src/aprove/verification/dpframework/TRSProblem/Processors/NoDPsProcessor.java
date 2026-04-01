package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

/**
 * Processor which trivially checks for termination by
 * testing DPs(R) = emptyset
 */
@NoParams
public class NoDPsProcessor extends QTRSProcessor {

    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        return qtrs.getDPs().x.isEmpty();
    }

    @Override
    protected Result processQTRS(final QTRSProblem qtrs, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        final QDPProblem qdpProblem = QDPProblem.create(qtrs.getDPs().x, qtrs, true);
        return ResultFactory.proved(NoDPsProcessor.theProof);
    }

    private static Proof theProof = new NoDPsProof();

    private static class NoDPsProof extends QTRSProof {

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level){
            return eu.export("The TRS does not have any Dependency Pairs "+eu.cite(Citation.AG00)+". Thus it is terminating.");
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            return CPFTag.TRS_TERMINATION_PROOF.create(
                doc,
                CPFTag.DP_TRANS.create(
                    doc,
                    CPFTag.dps(doc, xmlMetaData, new ArrayList<Rule>()),
                    CPFTag.MARKED_SYMBOLS.create(doc, doc.createTextNode("true")),
                    CPFTag.DP_PROOF.create(doc, CPFTag.P_IS_EMPTY.create(doc))));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }

    }
}
