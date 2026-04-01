package aprove.verification.dpframework.MCSProblem.Processors;

import java.util.*;
import java.util.logging.Logger;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.MCSProblem.*;
import aprove.verification.dpframework.MCSProblem.mcnp.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Uses Igor Gonopolskiy's SAT-based MCNP prototype to show termination
 * of MCS problems.
 *
 * TODO Same thing on IDPProblem level:
 * - abstract 1 rule r from P to 1 or more rules abs(r) in the MCS
 * - deleting all rules from abs(r) from MCS means deleting r from P
 *
 * Currently we would get 1 subproblem where both strictness and
 * boundedness allowed us to delete an edge -- if different edges
 * are concerned, we may get 2 subproblems (CADE'07 / RTA'09 style).
 * TODO Check whether this makes a difference in practice.
 *
 * @author fuhs
 */
public class MCSMCNPProcessor extends MCSProblemProcessor implements Processor {

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.MCSProblem.Processors.MCSMCNPProcessor");

    @Override
    public boolean isMCSApplicable(MCSProblem mcs) {
        return true;
    }

    @Override
    protected Result processMCSProblem(MCSProblem mcs, Abortion aborter)
            throws AbortionException {
        // - translate to mcs programs
        Config.silenceMode();
        Program mcProgram = Program.createFromMCSProblem(mcs);

        // - find ranking structure
        long nanos = System.nanoTime();
        mcProgram.findLevelMappings();
        nanos = System.nanoTime() - nanos;
        MCSMCNPProcessor.log.finer("Searching for MCNP ranking function took " + nanos/1000000 + " ms.");
        List<MCGraphMapping> rankingFunction = mcProgram.getMcGraphsMappings();
        if (rankingFunction == null) {
            return ResultFactory.unsuccessful();
        }

        // - verify ranking structure
        nanos = System.nanoTime();
        Verifier ver = new Verifier();
        ver.verify(mcProgram.getInitialMCGraphs(), rankingFunction);
        nanos = System.nanoTime() - nanos;
        MCSMCNPProcessor.log.finer("Verifying MCNP ranking function took " + nanos/1000000 + " ms.");

        // - export ranking structure as proof of termination
        Proof proof = new MCSMCNPProof(rankingFunction);
        return ResultFactory.proved(proof);
    }

    private static class MCSMCNPProof extends Proof.DefaultProof {

        private final List<MCGraphMapping> rankingFunction;

        private MCSMCNPProof(List<MCGraphMapping> rankingFunction) {
            this.rankingFunction = rankingFunction;
        }

        @Override
        public String export(Export_Util eu, VerbosityLevel level) {
            StringBuilder res = new StringBuilder();
            int i = 0;
            for (MCGraphMapping mcgm : this.rankingFunction) {
                ++i;
                res.append("Level Mapping ").append(i).append(':');
                res.append(eu.newline()).append(eu.export(mcgm));
                res.append(eu.newline());
            }
            return res.toString();
        }
    }
}
