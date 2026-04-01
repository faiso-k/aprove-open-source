package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Utility.*;
import aprove.verification.dpframework.TRSProblem.Utility.OutermostTerminationGraph.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * (Debug-Outputs: DEBUG_SEBWEI)
 *
 * this Processor tries to transform an OTRSProblem into a Set of QDPProblems
 *      by trying to build an OutermostTerminationGraph and extracting QDPProblems from it
 *
 * @author Sebastian Weise
 */

public class OTRSToQDPTerminationGraphProcessor extends OTRSProcessor {

    /**
     * Parameters for initializing the OutermostTerminationGraph;
     *
     * "pathForDebugOutputs" needs only to be set properly if Debug-Mode is activated;
     *      otherwise can be set arbitrarily, e.g. = ""
     */
    private final Strategy strategy;
    private final int maxNodesBeforeFinalization;
    private final Boolean useExclusionSubstitutions;
    private final String pathForDebugOutputs;

    /**
     * Default-Values:
     *      Strategy                    = Linearize
     *      MaxNodesBeforeFinalization  = 100
     *      UseExclusionSubstitutions   = True
     *      PathForDebugOutputs         = "/tmp"
     *
     * @param pathForDebugOutputs needs only to be set properly if Debug-Mode is activated;
     *                              otherwise can be set arbitrarily, e.g. = ""
     */
    @ParamsViaArguments( { "Strategy", "MaxNodesBeforeFinalization",
        "UseExclusionSubstitutions", "PathForDebugOutputs" })
    public OTRSToQDPTerminationGraphProcessor(final Strategy strategy,
            final int maxNodesBeforeFinalization,
            final Boolean useExclusionSubstitutions,
            final String pathForDebugOutputs) {

        this.strategy = strategy;
        this.maxNodesBeforeFinalization = maxNodesBeforeFinalization;
        this.useExclusionSubstitutions = useExclusionSubstitutions;
        this.pathForDebugOutputs = pathForDebugOutputs;
    }

    @Override
    public boolean isOTRSApplicable(final OTRSProblem R) {
        if (Options.certifier.isCeta()) {
            return false;
        }
        // check Variable-Condition
        for (final GeneralizedRule actGeneralizedRule : R.getR()) {
            if (!(actGeneralizedRule instanceof Rule)) {
                return false;
            }
        }
        return true;
    }

    @Override
    protected Result processOTRS(final OTRSProblem R,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException {

        final OutermostTerminationGraph outermostTerminationGraph =
            new OutermostTerminationGraph(R, this.strategy,
                this.maxNodesBeforeFinalization,
                this.useExclusionSubstitutions, this.pathForDebugOutputs);

        if (aprove.Globals.DEBUG_SEBWEI) {
            // write the Path of our OTRSPRoblem into a file
            outermostTerminationGraph.getUtil().printDebugFile("Path",
                (String) rti.getMetadata(Metadata.PROBLEM_PATH_NAME));
        }

        if (!outermostTerminationGraph.getBuildFailed()) {
            final Set<QDPProblem> qdpProblems =
                outermostTerminationGraph.extractQDPProblems();
            return ResultFactory.provedAnd(qdpProblems,
                YNMImplication.SOUND, new OutermostTerminationProof());
        } else {
            return ResultFactory.unsuccessful("Failed building an Outermost-Terminationgraph.");
        }
    }

    private class OutermostTerminationProof extends QTRSProof {

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            return "Transforming the OTRSProblem into a Set of QDPProblems by building an Outermost-Terminationgraph (successfully) and extracting QDPProblems from it.";
        }
    }
}