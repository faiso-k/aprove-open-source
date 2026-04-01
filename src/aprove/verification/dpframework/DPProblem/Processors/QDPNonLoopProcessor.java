package aprove.verification.dpframework.DPProblem.Processors;

import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Utility.NonLoop.NonLoopSearch.*;
import aprove.verification.dpframework.Utility.NonLoop.heuristic.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.nontermination.*;

/**
 * <p>
 * This processor is the implementation of the techniques of the paper
 * "Proving Non-Looping Non-Termination Automatically" <br>
 * by Fabian Emmes, Tim Enger and Jürgen Giesly<br>
 * <br>
 * based on: Bachelor thesis:<br>
 * <b>"Detecting Non-Termination of Non-Looping Term Rewrite Systems"</b><br>
 * by Tim Enger
 * </p>
 * <p>
 * It is able to use different {@link NonLoopSearch search techniques} for
 * finding a non-loop and show non-termination.
 * </p>
 *
 * @author Tim Enger
 */

public class QDPNonLoopProcessor extends QDPProblemProcessor {

    /**
     * arguments from strategy
     */
    private final Arguments args;

    /**
     * logger to be used
     */
    private final Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.QDPNonLoopProcessor");

    /**
     * Constructor
     *
     * @param argsArg
     *            See {@link Arguments}
     */
    @ParamsViaArgumentObject
    public QDPNonLoopProcessor(final Arguments argsArg) {
        this.args = argsArg;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        return qdp.getQ().isEmpty();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected Result processQDPProblem(final QDPProblem qdp, final Abortion aborter) throws AbortionException {

        if (Globals.DEBUG_NEX) {
            System.err.println("QDPNonLoopProcessor started on:");
            System.err.println(qdp);
        }

        final IterativeDeepeningNonLoopSearch searchMethod =
            new IterativeDeepeningNonLoopSearch(qdp, aborter, this.log, new PassedNonLoopHeuristic(this.args.NARROWING,
                Arguments.F_NARROWING, Arguments.B_NARROWING, Arguments.ALLOWVARPOS, this.args.MAXITERATIONS));

        this.log.info("QDPNonLoopProcessor started with the search method:");
        this.log.info(searchMethod.getDescription());

        final NonLoopProof nonLoop = searchMethod.findNonLoop();

        if (nonLoop != null) {
            // set obligation for export
            nonLoop.setObligation(qdp);
            return ResultFactory.disproved(nonLoop);
        } else {
            return ResultFactory.unsuccessful("Could not find a non-loop");
        }

    }

    /**
     * Class for strategy arguments.
     *
     * @author Tim Enger
     */
    public static class Arguments {
        /**
         * Narrowings Steps in "Pre-Processing"
         */
        public int NARROWING = 3;

        /**
         * If true, the full proof is shown with every detail. Otherwise,
         * intermediate steps are omitted.
         */
        public boolean FULLPROOF = false;

        /**
         * The maximum number of iterations the processor should make.
         */
        public int MAXITERATIONS = -1; // less than 1 --> infinity iterations

        /**
         * Flag to indicate if Forward Narrowing should be used
         */
        public static final boolean F_NARROWING = true;

        /**
         * Flag to indicate if Backward Narrowing should be used
         */
        public static final boolean B_NARROWING = false;

        /**
         * Flag to indicate if narrowing into variables is permitted
         */
        public static final boolean ALLOWVARPOS = false;

    }
}
