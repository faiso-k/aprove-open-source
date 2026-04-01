package aprove.verification.dpframework.PATRSProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.PADPProblem.*;
import aprove.verification.dpframework.PATRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Processor that transforms a PATRS into a PADPProblem containing all dependency pairs.
 *
 * @author Stephan Falke
 * @version $Id$
 */
@NoParams
public class PATRSDPProcessor extends PATRSProcessor {

    protected static Logger logger = Logger.getLogger("aprove.verification.dpframework.PATRSProblem.Processors.PADPProcessor");

    @Override
    protected Result processPATRS(PATRSProblem patrs, Abortion aborter) throws AbortionException {
        PATRSDPProcessor.logger.log(Level.FINE, "Creating dependency pairs\n");
        Pair<ImmutableSet<PARule>, Map<FunctionSymbol, FunctionSymbol>> dppair = patrs.getDPs();
        PADPProblem padp = PADPProblem.create(dppair.x, patrs, dppair.y);
        return ResultFactory.proved(padp, YNMImplication.EQUIVALENT, new PATRSDPProof(padp));
    }

    private class PATRSDPProof extends Proof.DefaultProof {
        PADPProblem padp;

        private PATRSDPProof(PADPProblem padp) {
            this.padp = padp;
        }

        @Override
        public String export(Export_Util eu, VerbosityLevel level){
            return "Using the dependency pair approach we obtain in the following initial PADP problem:" +
                   eu.linebreak() + this.padp.export(eu) + eu.linebreak();
        }
    }

}
