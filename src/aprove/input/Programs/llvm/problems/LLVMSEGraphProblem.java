package aprove.input.Programs.llvm.problems;

import java.util.Map;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A symbolic execution graph generated from some LLVM program and a start function.
 * @author Marc Brockschmidt
 */
public class LLVMSEGraphProblem
    extends DefaultBasicObligation
    implements DOT_Able, VariableRenaming {

    /**
     * A graph created from a llvm program using some start state.
     */
    protected final LLVMSEGraph graph;

    /**
     * Flag indicating whether or not the graph should be rendered.
     */
    protected final boolean renderGraph;

    /**
     * The variable renaming carried out when creating this problem
     */
    protected final CollectionMap<String, String> variableRenaming = new CollectionMap<>();

    /**
     * @param graphParam a graph created by symbolic evaluation of some program.
     * @param renderGraphParam Flag indicating whether or not the graph should be rendered.
     */
    public LLVMSEGraphProblem(final LLVMSEGraph graphParam, final boolean renderGraphParam) {
        super("LLVM Symbolic Execution Graph", "New LLVM Symbolic Execution Graph problem");
        assert (graphParam != null);
        this.graph = graphParam;
        this.renderGraph = renderGraphParam;
    }

    /**
     * SV-COMP: Write SV-COMP witness to GraphML file
     */
    public String buildGraphMLWitness(Map<String, LLVMHeuristicConstRef> varAssign, Abortion aborter) {
        // if no variable assignment for the graph is found, stop generating immediately
        if (varAssign == null || varAssign.isEmpty()) {
            return null;
        }

        return GraphMLWitnessBuilder.buildGraphMLWitness(this.graph, this.graph.getNodes(), null, varAssign, aborter);
    }

    /**
     * Export our knowledge from the termination graph.
     * @param o export util
     * @return textual representation of the FI graph
     */
    @Override
    public String export(Export_Util eu) {
        return "Symbolic Execution Graph";
//    	if(graph.getNodes().size() < 500) {
//    		return this.graph.export("Symbolic Execution Graph based on LLVM Program:", this.renderGraph, eu);
//    	} else {
//    		return eu.export("Graph too large for export");
//    	}
        //return "SE Graph";
    }

    /**
     * @return the termination graph containing the individual
     * {@link MethodGraph}s
     */
    public LLVMSEGraph getGraph() {
        return this.graph;
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
        return null;
    }

    @Override
    public String toDOT() {
        return this.graph.toDOT();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public CollectionMap<String, String> getVariableRenaming() {
        return this.variableRenaming;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void setVariableRenaming(CollectionMap<String, String> variableRenaming) {
        this.variableRenaming.putAll(variableRenaming);
    }
}
