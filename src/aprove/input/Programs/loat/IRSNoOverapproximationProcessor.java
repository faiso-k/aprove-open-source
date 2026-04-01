package aprove.input.Programs.loat;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * This processor serves as a filter:
 * If the IRSProblem over-approximates, a proof of non-termination cannot succeed. 
 * In that case this processor aborts further computation prematurely. 
 * 
 * @author Constantin Mensendiek
 */
public class IRSNoOverapproximationProcessor extends Processor.ProcessorSkeleton{

    @Override
    public Result process(BasicObligation obl,
                          BasicObligationNode oblNode,
                          Abortion aborter,
                          RuntimeInformation rti) throws AbortionException {
        assert !Globals.useAssertions || obl instanceof IRSProblem;

        IRSProblem problem = (IRSProblem) obl;
        
        if(!problem.getOverapproximates()) {
            return ResultFactory.provedAnd(Collections.singletonList(problem),
                                           YNMImplication.EQUIVALENT,
                                           new IRSNoOverapproximationProof(false));
        } else {
            return ResultFactory.unknown(new IRSNoOverapproximationProof(true));
        }
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof IRSProblem;
    }
    
    public static class IRSNoOverapproximationProof extends DefaultProof {

        private boolean overapproximates;

        public IRSNoOverapproximationProof(boolean overapproximates) {
            this.shortName = "IRSNoOverapproximation";
            this.longName = "stops computation if IRS over-approximates";
            this.overapproximates = overapproximates;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            if(overapproximates) {
                return "Proof of non-termination is aborted since the IRSProblem over-approximates";
            } else {
                return "Proof of non-termination can continue";
            }
        }
    }

}
