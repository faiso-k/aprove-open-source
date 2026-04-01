package aprove.verification.dpframework.PATRSProblem.Processors;

import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.PATRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Processor that just throws mu away.
 *
 * @author Stephan Falke
 * @version $Id$
 */
@NoParams
public class CSPATRSToPATRSProcessor extends CSPATRSProcessor {

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.PATRSProblem.Processors.CSPATRSToTRSProcessor");

    @Override
    protected Result processCSPATRS(CSPATRSProblem patrs, Abortion aborter) throws AbortionException {
        Proof proof = new CSPATRSToPATRSProof();
        PATRSProblem newPATRS = PATRSProblem.create(patrs.getR(), patrs.getS(), patrs.getE(), patrs.getSortMap());

        return ResultFactory.proved(newPATRS, YNMImplication.SOUND, proof);
    }

    private static class CSPATRSToPATRSProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            result.append("By disregarding the replacement map we obtain a PATRS problem.");
            return result.toString();
        }
    }

}
