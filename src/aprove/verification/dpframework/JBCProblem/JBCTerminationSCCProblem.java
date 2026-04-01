package aprove.verification.dpframework.JBCProblem;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Processors.ToSCC.*;

/**
 * A TerminationGraph generated from some program and start term.
 * @author Marc Brockschmidt
 */
public class JBCTerminationSCCProblem extends DefaultBasicObligation {
    /**
     * The considered SCC.
     */
    private final JBCGraph scc;

    /**
     * The full graph that needs to be considered (including helper methods).
     */
    private final JBCGraph fullGraph;

    /**
     * Methods that are part of the SCC.
     */
    private final Set<MethodGraph> sccGraphs;

    /**
     * Set of edges that represent calls to other method graphs that are not
     * part of the SCC.
     */
    private final Set<Edge> outgoingCallEdges;

    /**
     * Set of edges that represent returns from other method graphs that are
     * not part of the SCC.
     */
    private final Set<Edge> incomingReturnEdges;

    /**
     * Called helper methods.
     */
    private final Set<MethodGraph> helperGraphs;

    /**
     * The annotations for this SCC.
     */
    private final SCCAnnotations sccAnnotations;

    /**
     * The start node, if such a node exists for this problem.
     */
    private final Node startNode;

    /**
     * @param s some SCC in a termination graph.
     * @param fullG the full graph that needs to be considered (including helper
     *  methods).
     * @param sccGs set of methods that are part of the SCC.
     * @param outCalls set of edges that represent calls to other method graphs
     *  that are not part of the SCC.
     * @param inReturns set of edges that represent returns from other method
     *  graphs that are not part of the SCC.
     * @param helperGs set of helper methods that are (indirectly) used by the
     *  SCC.
     * @param sccAnn annotations for this SCC.
     * @param isBounded marks if the graph was obtained using bounded integer arithmetic.
     * @param start the start node of the problem, if one exists (otherwise, use null)
     */
    public JBCTerminationSCCProblem(final JBCGraph s, final JBCGraph fullG, final Set<MethodGraph> sccGs,
            final Set<Edge> outCalls, final Set<Edge> inReturns, final Set<MethodGraph> helperGs,
            final SCCAnnotations sccAnn, final Node start) {
        super("JBCTerminationSCC", "New JBC Termination Graph SCC problem");
        this.scc = s;
        this.fullGraph = fullG;
        this.sccGraphs = sccGs;
        this.outgoingCallEdges = outCalls;
        this.incomingReturnEdges = inReturns;
        this.helperGraphs = helperGs;
        this.sccAnnotations = sccAnn;
        this.startNode = start;
    }

    /**
     * @return the considered SCC.
     */
    public JBCGraph getSCC() {
        return this.scc;
    }

    /**
     * @return the full graph that needs to be considered (including helper
     *  methods).
     */
    public JBCGraph getFullGraph() {
        return this.fullGraph;
    }

    /**
     * @return the edges that represent calls to other method graphs that are
     * not part of the SCC.
     */
    public Set<Edge> getOutgoingCallEdges() {
        return this.outgoingCallEdges;
    }

    /**
     * @return the edges that represent returns from other method graphs that
     * are not part of the SCC.
     */
    public Set<Edge> getIncomingReturnEdges() {
        return this.incomingReturnEdges;
    }

    /**
     * @return the called helper methods.
     */
    public Set<MethodGraph> getHelperGraphs() {
        return this.helperGraphs;
    }

    /**
     * @return the annotations for this SCC.
     */
    public SCCAnnotations getSCCAnnotations() {
        return this.sccAnnotations;
    }

    /**
     * Export our knowledge from the termination graph.
     * @param o export util
     * @return textual representation of the FI graph
     */
    @Override
    public String export(final Export_Util o) {
        final StringBuilder sb = new StringBuilder();
        sb.append("SCC of termination graph based on JBC Program.").append(o.linebreak());

        sb.append("SCC contains nodes from the following methods: ");
        boolean first = true;
        for (final MethodGraph mg : this.sccGraphs) {
            if (!first) {
                sb.append(", ");
            }
            sb.append(o.escape(mg.getParsedMethod().getMethodIdentifier().toString()));
            first = false;
        }
        sb.append(o.linebreak());

        sb.append("SCC calls the following helper methods: ");
        first = true;
        for (final MethodGraph mg : this.helperGraphs) {
            if (!first) {
                sb.append(", ");
            }
            sb.append(o.escape(mg.getParsedMethod().getMethodIdentifier().toString()));
            first = false;
        }
        sb.append(o.linebreak());

        sb.append("Performed SCC analyses:").append(o.linebreak());
        final List<String> analysisOutput = new LinkedList<String>();
        for (final SCCAnalysis a : this.sccAnnotations.getAnalyses()) {
            analysisOutput.add(a.export(o));
        }
        sb.append(o.set(analysisOutput, Export_Util.ITEMIZE));

        return sb.toString();
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Termination");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "jbcGraphSCC";
    }

    /**
     * @return start node of the problem, if one exists (otherwise, null)
     */
    public Node getStartNode() {
        return this.startNode;
    }
}
