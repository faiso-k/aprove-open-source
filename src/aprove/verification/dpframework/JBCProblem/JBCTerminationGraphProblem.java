package aprove.verification.dpframework.JBCProblem;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A TerminationGraph generated from some program and start term.
 * @author Marc Brockschmidt
 */
public class JBCTerminationGraphProblem extends DefaultBasicObligation implements DOTmodern_Able {
    /**
     * A graph created from a jbcProgram using some start state.
     */
    private final TerminationGraph graph;

    private CollectionMap<Node, AbstractVariableReference> relevanceInfo;

    /**
     * @param graphParam a graph created by symbolic evaluation of some program.
     * @param complexityAnalysis whether this is a complexity (in contrast to termination) obligation.
     */
    public JBCTerminationGraphProblem(final TerminationGraph graphParam) {
        super("JBCTerminationGraph", "New JBC Termination Graph problem");
        this.graph = graphParam;
    }

    public JBCTerminationGraphProblem(TerminationGraph graphParam, CollectionMap<Node, AbstractVariableReference> relevanceInfo) {
        this(graphParam);
        this.relevanceInfo = relevanceInfo;
    }

    /**
     * @return the termination graph containing the individual
     * {@link MethodGraph}s
     */
    public TerminationGraph getGraph() {
        return this.graph;
    }

    /**
     * Export our knowledge from the termination graph.
     * @param o export util
     * @return textual representation of the FI graph
     */
    @Override
    public String export(final Export_Util o) {
        final StringBuilder sb = new StringBuilder();
        sb.append("Termination Graph based on JBC Program:");
        sb.append(o.linebreak());
        sb.append(this.graph.export(o));
        sb.append(o.linebreak());
        return sb.toString();
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Termination");
    }

    @Override
    public String toDOT() {
        return this.graph.toDOT();
    }
    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        switch (graph.getGoal()) {
            case Termination: return "jbcTermGraph";
            case RuntimeComplexity:
            case UserDefined:
            case SpaceComplexity: return "jbcComplexityGraph";
            default: throw new RuntimeException(graph.getGoal() + " not supported for JBC");
        }
    }

    public CollectionMap<Node, AbstractVariableReference> getRelevanceInfo() {
        return relevanceInfo;
    }
}
