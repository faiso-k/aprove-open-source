package aprove.input.Programs.prolog;

import org.json.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Utility.JSON.*;

/**
 * TODO this class is not immutable, but should be as it is a default obligation!
 * @author unknown, cryingshadow
 * @version $Id$
 */
public class PrologGraphProblem extends DefaultBasicObligation implements DOTmodern_Able, JSONExport {

    /**
     * The graph.
     */
    private PrologEvaluationGraph graph;

    public PrologGraphProblem(PrologEvaluationGraph graph) {
        this.graph = graph;
    }

    @Override
    public String export(Export_Util eu) {
        final StringBuilder sb = new StringBuilder();
        sb.append("Termination Graph based on Prolog Program:");
        sb.append(eu.linebreak());
        sb.append(eu.export(this.graph));
        sb.append(eu.linebreak());
        return sb.toString();
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "");
    }

    @Override
    public String getStrategyName() {
        // there is no default strategy
        return null;
    }

    @Override
    public String toDOT() {
        return this.graph.toInteractiveDOTwithEdges();
    }

    @Override
    public JSONObject toJSON() {
        return this.graph.toJSON();
    }

}
