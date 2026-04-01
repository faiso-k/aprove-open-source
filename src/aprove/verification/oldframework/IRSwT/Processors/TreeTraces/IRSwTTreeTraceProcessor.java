package aprove.verification.oldframework.IRSwT.Processors.TreeTraces;

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
 * Tries to find a termination tree trace
 * in the given input IRSwT. If this is successful,
 * then termination is shown.
 * @author Matthias Hoelzel
 */
public class IRSwTTreeTraceProcessor extends Processor.ProcessorSkeleton {
    /** Constructor! */
    public IRSwTTreeTraceProcessor() {
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return (obl != null && obl instanceof IRSwTProblem && !((IRSwTProblem) obl).isBounded());
    }

    @Override
    public Result process(final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException {
        assert obl instanceof IRSwTProblem : "Wrong obligation type!";
        final IRSwTProblem irswt = (IRSwTProblem) obl;

        final TreeTraceGenerator ttg = new TreeTraceGenerator(irswt);

        TreeTrace tt = ttg.generateNextTrace();
        while (tt != null) {
            final TreeTraceDecisionProcedure ttdp = new TreeTraceDecisionProcedure(tt);
            System.err.println(tt.getRules());
            final YNM result = ttdp.decideTermination();
            System.err.println(" => " + result);
            if (result == YNM.YES) {
                return ResultFactory.proved(new TreeTraceProof());
            }
            tt = ttg.generateNextTrace();
        }

        return ResultFactory.unsuccessful();
    }

    /**
     * A truly pathetic proof!
     * @author Matthias Hoelzel
     */
    public class TreeTraceProof extends DefaultProof {

        /** Constructor! */
        public TreeTraceProof() {
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append(eu.tttext("Found a terminating tree trace!"));
            return sb.toString();
        }
    }
}
