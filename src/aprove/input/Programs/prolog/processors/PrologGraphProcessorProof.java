package aprove.input.Programs.prolog.processors;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.JSON.*;

/**
 * Proof skeleton for processors based on symbolic evaluation graphs.
 * @author CryingShadow
 */
public abstract class PrologGraphProcessorProof extends DefaultProof implements DOT_Able {

    private final int exportLimit;

    private final PrologEvaluationGraph graph;

    private final Map<Integer, String> nodeLabels;

    public PrologGraphProcessorProof(PrologEvaluationGraph petGraph, boolean exportGraph, int exportLimit) {
        this(petGraph, exportGraph, exportLimit, new LinkedHashMap<Integer, String>());
    }

    public PrologGraphProcessorProof(
        PrologEvaluationGraph petGraph,
        boolean exportGraph,
        int exportLimit,
        Map<Integer, String> nodeLabels
    ) {
        this.graph = petGraph;
        this.exportLimit = exportLimit;
        this.nodeLabels = nodeLabels;
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {
        this.startUp();
        this.result.append(this.getProofMessage() + o.newline());
        if (o instanceof HTML_Util) {
            this.result.append("<textarea cols=\"80\" rows=\"25\">");
            this.result.append(this.graph.toInteractiveDOTwithEdges(true, this.nodeLabels));
            this.result.append("</textarea>");
        } else {
            this.result.append(o.export(JSONExportUtil.toJSONString(this.graph)));
            this.result.append(o.linebreak());
        }
        return this.result.toString();
    }

    @Override
    public String toDOT() {
        return this.graph.toInteractiveDOTwithEdges(true, this.nodeLabels);
    }

    /**
     * Returns the proof message before the graph output.
     * @return The proof message before the graph output.
     */
    protected abstract String getProofMessage();

}
