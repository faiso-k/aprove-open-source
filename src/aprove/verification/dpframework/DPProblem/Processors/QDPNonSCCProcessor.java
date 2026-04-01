package aprove.verification.dpframework.DPProblem.Processors;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

/**
 * For Rainbow certification. Check if the input problem's dependency
 * graph is an SCC, otherwise return YES. Use directly after the
 * dependency graph transformation (inside MAYBE, to allow the
 * remaining strategy to continue otherwise).
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
@NoParams
public class QDPNonSCCProcessor extends QDPProblemProcessor {
    @Override
    public boolean isQDPApplicable(QDPProblem qdp) {
        return !qdp.getDependencyGraph().isGenuineSCC();
    }

    @Override
    protected Result processQDPProblem(QDPProblem qdp, Abortion aborter)
            throws AbortionException {
        return ResultFactory.proved(new QDPNonSCCProof());
    }

    public static class QDPNonSCCProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "This is only a trivial SCC; it cannot have an infinite reduction sequence.";
        }

        @Override
        public Element toDOM(Document doc, XMLMetaData xmlMetaData) {
            return XMLTag.QDP_NON_SCC.createElement(doc);
        }
    }
}
