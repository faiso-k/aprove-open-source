package aprove.input.Programs.prolog.processors.toirswt;

import java.util.*;
import java.util.logging.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.graph.rules.*;
import aprove.input.Programs.prolog.processors.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class PrologToIRSwTTransformer extends PrologGraphProcessor {
    private static final Logger log =
        Logger.getLogger(PrologToIRSwTTransformer.class.getName());

    @ParamsViaArgumentObject
    public PrologToIRSwTTransformer(final PrologOptions args) {
        super(args);
    }

    @Override
    protected Logger getLogger() {
        return PrologToIRSwTTransformer.log;
    }

    @Override
    protected Result processGraph(PrologEvaluationGraph graph, Abortion aborter)
            throws AbortionException {

        for(Node<PrologAbstractState> node : graph.getNodes()) {
            if(graph.isGeneralizationNode(node)) {
                // Copy the set of edges in order to be able to iterate over it and delete it at the same time
                final Collection<Edge<AbstractInferenceRule, PrologAbstractState>> edges = new LinkedList<>(graph.getOutEdges(node));
                for(Edge<AbstractInferenceRule, PrologAbstractState> edge : edges) {
                    if(edge.getObject().rule() != AbstractInferenceRules.GENERALIZATION) {
                        graph.removeEdge(edge);
                    }
                }
            }
        }

        final Collection<IRSwTProblem> resultingProblems = GraphToIRSwTConverter.create(aborter).convert(graph);

        final Proof proof = new PrologToIRSwTTransformerProof(graph, this.options.isExportTree(), this.options.getTreeLimit(), new HashMap<Integer, String>());
        return ResultFactory.provedAnd(resultingProblems, YNMImplication.SOUND, proof);
    }

    @Override
    public boolean isPrologApplicable(PrologProblem pp) {
        return pp.getQuery().getPurpose().equals(PrologPurpose.TERMINATION);
    }

}
