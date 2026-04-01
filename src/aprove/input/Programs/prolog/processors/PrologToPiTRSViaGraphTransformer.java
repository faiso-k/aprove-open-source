package aprove.input.Programs.prolog.processors;

import java.util.*;
import java.util.logging.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.graph.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * The PrologToLPTransformer builds a PrologDerivationGraph
 * and extracts a definite PrologProgram from it whose termination
 * guarantees termination of the original PrologProgram.
 * <br><br>
 *
 * @author cryingshadow
 * @version $Id$
 */

public class PrologToPiTRSViaGraphTransformer extends PrologGraphProcessor {

    /**
     * @author cryingshadow
     * Proof for this processor.
     */
    public class PrologToPiTRSViaGraphTransformerProof extends PrologGraphProcessorProof implements DOT_Able {

        /**
         * Standard constructor.
         * @param petGraph The graph.
         * @param exportGraph Flag indicating whether to export the graph graphically.
         * @param exportLimit Limit on the number of nodes up to which the graph is exported graphically (if at all).
         * @param nodeLabels To keep the connection between the graph and the proof.
         */
        public PrologToPiTRSViaGraphTransformerProof(
            final PrologEvaluationGraph petGraph,
            final boolean exportGraph,
            final int exportLimit,
            final Map<Integer, String> nodeLabels)
        {
            super(petGraph, exportGraph, exportLimit, nodeLabels);
        }

        @Override
        protected String getProofMessage() {
            // TODO: add citation
            return "Transformed Prolog program to (Pi-)TRS.";
        }

    }

    /**
     * Logger.
     */
    private static final Logger log =
        Logger.getLogger("aprove.input.Programs.prolog.processors.PrologToPiTRSViaGraphTransformer");

    /**
     * Standard constructor.
     * @param args The arguments of this processor.
     */
    @ParamsViaArgumentObject
    public PrologToPiTRSViaGraphTransformer(final PrologOptions args) {
        super(args);
    }

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return pp.getQuery().getPurpose().equals(PrologPurpose.TERMINATION);
    }

    @Override
    protected Logger getLogger() {
        return PrologToPiTRSViaGraphTransformer.log;
    }

    @Override
    protected Result processGraph(final PrologEvaluationGraph graph, final Abortion aborter) throws AbortionException {
        long time = 0;
        if (PrologToPiTRSViaGraphTransformer.log.isLoggable(Level.FINE)) {
            time = System.nanoTime();
        }
        final Collection<BasicObligation> obs = new ArrayList<BasicObligation>();
        final Map<Integer, String> nodeLabels = new LinkedHashMap<Integer, String>();
        final PrologProblem pp =
            PrologToLPTransformer.calculateProblemFromGraph(graph, nodeLabels, this.options.getSmt(), aborter);
        if (pp == null) {
            return ResultFactory.aborted("program extraction took too long");
        }
        if (this.options.isTrs()) {
            obs.add(QTRSProblem.create(ImmutableCreator.create(PrologToTRSTransformer.calculateTRSFromGraph(
                graph,
                nodeLabels,
                aborter))));
        }
        final Afs afs = pp.createListOfAfs().get(0);
        final PrologFNG fridge1 = new PrologFNG(new LinkedHashSet<String>(), FreshNameGenerator.PROLOG_FUNCS);
        final PrologToPiTRSTransformer.Arguments params1 = new PrologToPiTRSTransformer.Arguments();
        // 0: false, 1: true, 2: false (and second proc with true)
        params1.force = this.options.getForce() == 1;
        final PrologToPiTRSTransformer proc1 = new PrologToPiTRSTransformer(params1);
        obs.add(proc1.calculatePiTRSProblem(pp, afs, fridge1).x);
        if (this.options.getForce() == 2) {
            final PrologFNG fridge2 = new PrologFNG(new LinkedHashSet<String>(), FreshNameGenerator.PROLOG_FUNCS);
            final PrologToPiTRSTransformer.Arguments params2 = new PrologToPiTRSTransformer.Arguments();
            params2.force = true;
            final PrologToPiTRSTransformer proc2 = new PrologToPiTRSTransformer(params2);
            obs.add(proc2.calculatePiTRSProblem(pp, afs, fridge2).x);
        }
        if (PrologToPiTRSViaGraphTransformer.log.isLoggable(Level.FINE)) {
            time = System.nanoTime() - time;
            PrologToPiTRSViaGraphTransformer.log.log(Level.FINE, "Reading new PrologProblem: {0}ms\n", time / 1000000);
            time = System.nanoTime();
        }
        final Proof proof =
            new PrologToPiTRSViaGraphTransformerProof(
                graph,
                this.options.isExportTree(),
                this.options.getTreeLimit(),
                nodeLabels);
        return obs.size() == 1
            ? ResultFactory.proved(obs.iterator().next(), YNMImplication.SOUND, proof)
                : ResultFactory.provedOr(obs, YNMImplication.SOUND, proof);
    }

}
