package aprove.verification.dpframework.JBCProblem;

import static aprove.verification.oldframework.Input.HandlingMode.*;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Processors.ToComplexity.*;
import aprove.verification.oldframework.Bytecode.Processors.ToSCC.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A TerminationGraph generated from some program and start term.
 * @author Marc Brockschmidt
 */
public class JBCGraphEdgesComplexityProblem extends DefaultBasicObligation {
    /**
     * The full graph that needs to be considered (including helper methods).
     */
    private final JBCGraph fullGraph;

    /**
     * The start of the computation (may be null)
     */
    private final Node startNode;

    /**
     * Set of edges that are to be encoded.
     */
    private final Set<Edge> edgesToEncode;

    /**
     * The annotations for this SCC.
     */
    private final SCCAnnotations sccAnnotations;

    private Collection<HandlingMode> supportedGoals = Arrays.asList(new HandlingMode[]{RuntimeComplexity, SpaceComplexity, SizeComplexity, UserDefined});

    private HandlingMode goal = HandlingMode.RuntimeComplexity;
    private Optional<ComplexityGoalTerm> goalTerm;
    private ConsideredPaths consideredPaths;

    private CollectionMap<Node, AbstractVariableReference> relevantRefs;

    /**
     * @param fullG the full graph that needs to be considered (including helper
     *  methods).
     * @param startN start of the computation (may be null)
     * @param edges set of edges that are to be encoded.
     * @param sccAnn annotations for this SCC.
     */
    protected JBCGraphEdgesComplexityProblem(
        final JBCGraph fullG,
        final Node startN,
        final Set<Edge> edges,
        final SCCAnnotations sccAnn,
        final CollectionMap<Node, AbstractVariableReference> relevantRefs,
        final ConsideredPaths consideredPaths)
    {
        super("JBCComplexityEdges", "New JBC Complexity problem");
        this.fullGraph = fullG;
        this.startNode = startN;
        this.edgesToEncode = edges;
        this.sccAnnotations = sccAnn;
        this.relevantRefs = relevantRefs;
        this.consideredPaths = consideredPaths;
    }

    public static JBCGraphEdgesComplexityProblem create(
        JBCGraph fullG,
        Node startN,
        Set<Edge> edges,
        SCCAnnotations sccAnn,
        CollectionMap<Node, AbstractVariableReference> relevantRefs) {
        return new JBCGraphEdgesComplexityProblem(fullG, startN, edges, sccAnn, relevantRefs, ConsideredPaths.ALL_PATHS_FROM_START);
    }

    public static JBCGraphEdgesComplexityProblem createCESExportable(
            JBCGraph fullG,
            Node startN,
            Set<Edge> edges,
            SCCAnnotations sccAnn,
            CollectionMap<Node, AbstractVariableReference> relevantRefs) {
            return new JBCGraphEdgesComplexityProblem(fullG, startN, edges, sccAnn, relevantRefs, ConsideredPaths.NONTERM_PATHS_AND_PATHS_FROM_START_TO_SINKS);
        }

    /**
     * @return the full graph that needs to be considered (including helper
     *  methods).
     */
    public JBCGraph getFullGraph() {
        return this.fullGraph;
    }

    /**
     * @return start of the computation (may be null)
     */
    public Node getStartNode() {
        return this.startNode;
    }

    /**
     * @return the set of edges that are to be encoded.
     */
    public Set<Edge> getEdgesToEncode() {
        return this.edgesToEncode;
    }

    /**
     * @return the annotations for this SCC.
     */
    public SCCAnnotations getSCCAnnotations() {
        return this.sccAnnotations;
    }

    /**
     * @param o export util
     * @return textual representation of the obligation
     */
    @Override
    public String export(final Export_Util o) {
        final StringBuilder sb = new StringBuilder();
        sb.append("Set of " + this.edgesToEncode.size() + " edges based on JBC Program.").append(o.linebreak());

        sb.append("Performed SCC analyses:").append(o.linebreak());
        final List<String> analysisOutput = new LinkedList<>();
        for (final SCCAnalysis a : this.sccAnnotations.getAnalyses()) {
            analysisOutput.add(a.export(o));
        }
        sb.append(o.set(analysisOutput, Export_Util.ITEMIZE));
        sb.append(o.newline());
        sb.append(o.export("Considered paths: "));
        sb.append(consideredPaths.export(o));
        return sb.toString();
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Termination");
    }

    @Override
    public String getStrategyName() {
        return "jbcGraphEdgesComplexity";
    }

    public void setGoal(HandlingMode goal, Optional<ComplexityGoalTerm> goalTerm) {
        assert supportedGoals.contains(goal) : goal + " not supported for JBC";
        this.goal = goal;
        this.goalTerm = goalTerm;
    }

    public HandlingMode getGoal() {
        return this.goal;
    }

    public Optional<ComplexityGoalTerm> getGoalTerm() {
        return this.goalTerm;
    }

    public CollectionMap<Node, AbstractVariableReference> getRelevantRefs() {
        return relevantRefs;
    }

    public ConsideredPaths consideredPaths() {
        return consideredPaths;
    }
}
