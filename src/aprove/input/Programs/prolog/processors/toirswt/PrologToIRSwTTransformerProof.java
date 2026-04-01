package aprove.input.Programs.prolog.processors.toirswt;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.processors.*;
import aprove.prooftree.Export.Utility.*;

public class PrologToIRSwTTransformerProof extends PrologGraphProcessorProof implements DOT_Able {

    /**
     * Standard constructor.
     * @param petGraph The graph.
     * @param exportGraph Flag indicating whether to export the graph graphically.
     * @param exportLimit Limit on the number of nodes up to which the graph is exported graphically (if at all).
     * @param nodeLabels To keep the connection between the graph and the proof.
     */
    public PrologToIRSwTTransformerProof(
        final PrologEvaluationGraph petGraph,
        final boolean exportGraph,
        final int exportLimit,
        final Map<Integer, String> nodeLabels)
    {
        super(petGraph, exportGraph, exportLimit, nodeLabels);
    }

    @Override
    protected String getProofMessage() {
        return "Transformed Prolog program to IRSwT according to method in Master Thesis of A. Weinert";
    }
}