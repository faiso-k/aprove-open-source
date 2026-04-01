package aprove.input.Programs.prolog.processors;

import java.util.logging.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.graph.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;

/**
 * The PrologDeterminacyProcessor tries to prove that the query in the given Prolog program has at most one solution.
 * <br><br>
 *
 * @author cryingshadow
 * @version $Id$
 */

public class PrologDeterminacyProcessor extends PrologGraphProcessor {

    /**
     * @author cryingshadow
     * Proof for this processor.
     */
    public class PrologDeterminacyProcessorProof extends PrologGraphProcessorProof implements DOT_Able {

        /**
         * Standard constructor.
         * @param petGraph The graph.
         * @param exportGraph Flag indicating whether to export the graph graphically.
         * @param exportLimit Limit on the number of nodes up to which the graph is exported graphically (if at all).
         */
        public PrologDeterminacyProcessorProof(
            final PrologEvaluationGraph petGraph,
            final boolean exportGraph,
            final int exportLimit)
        {
            super(petGraph, exportGraph, exportLimit);
        }

        @Override
        protected String getProofMessage() {
            // TODO: add citation
            return "The root node satisfies the determinacy criterion.";
        }

    }

    /**
     * Logger.
     */
    private static final Logger log =
        Logger.getLogger("aprove.input.Programs.prolog.processors.PrologDeterminacyProcessor");

    /**
     * Standard constructor.
     * @param args The arguments of this processor.
     */
    @ParamsViaArgumentObject
    public PrologDeterminacyProcessor(final PrologOptions args) {
        super(args);
    }

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return pp.getQuery().getPurpose().equals(PrologPurpose.DETERMINACY);
    }

    @Override
    protected Logger getLogger() {
        return PrologDeterminacyProcessor.log;
    }

    @Override
    protected Result processGraph(final PrologEvaluationGraph graph, final Abortion aborter) throws AbortionException {
        long time = 0;
        if (PrologDeterminacyProcessor.log.isLoggable(Level.FINE)) {
            time = System.nanoTime();
        }
        final boolean isDeterministic = graph.isDeterministic(graph.getRoot(), aborter);
        if (PrologDeterminacyProcessor.log.isLoggable(Level.FINE)) {
            time = System.nanoTime() - time;
            PrologDeterminacyProcessor.log.log(Level.FINE, "Checking DC: {0}ms\n", time / 1000000);
            time = System.nanoTime();
        }
        return
            isDeterministic ?
                ResultFactory.proved(
                    new PrologDeterminacyProcessorProof(
                        graph,
                        this.options.isExportTree(),
                        this.options.getTreeLimit()
                    )
                ) :
                    ResultFactory.unsuccessful("The root node does not satisfy the DC.");
    }

}
