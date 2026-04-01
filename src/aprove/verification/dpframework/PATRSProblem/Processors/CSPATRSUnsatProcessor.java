package aprove.verification.dpframework.PATRSProblem.Processors;

import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.PATRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Removes rewrite rules with an unsatisfiable constraint.
 *
 * @author Stephan Falke
 * @version $Id$
 */
@NoParams
public class CSPATRSUnsatProcessor extends CSPATRSProcessor {

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.PATRSProblem.Processors.CSPATRSUnsatProcessor");

    @Override
    protected Result processCSPATRS(CSPATRSProblem patrs, Abortion aborter) throws AbortionException {
        PATRSProblem plain = PATRSProblem.create(patrs.getR(), patrs.getS(), patrs.getE(), patrs.getSortMap());

        PATRSUnsatProcessor slave = new PATRSUnsatProcessor();
        Result res = slave.processPATRS(plain, aborter);

        ObligationNodeChild child = res.getObligationChild();

        if (child == null || child.getNewObligation() == null) {
            return ResultFactory.unsuccessful();
        } else {
            PATRSProblem newprob = (PATRSProblem) res.getSuccessPosition().getBasicObligation();
            CSPATRSProblem newCSPATRS = CSPATRSProblem.create(newprob.getR(), patrs.getS(), patrs.getE(), patrs.getSortMap(), patrs.getMu());
            return ResultFactory.proved(newCSPATRS, YNMImplication.EQUIVALENT, new CSPATRSUnsatProof(child.getProof()));
        }
    }

    private static class CSPATRSUnsatProof extends Proof.DefaultProof {

        private Proof child;

        private CSPATRSUnsatProof(Proof child) {
            this.child = child;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return this.child.export(o, level);
        }
    }

}
