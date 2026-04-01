package aprove.input.Programs.llvm.problems;

import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * An SCC of a symbolic execution graph generated from some program and start term.
 * @author Marc Brockschmidt, cryingshadow
 */
public class LLVMSCCProblem extends DefaultBasicObligation {

    /**
     * Flag indicating whether or not the SCC should be rendered.
     */
    protected final boolean renderSCC;

    /**
     * The considered SCC.
     */
    protected final SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> scc;

    /**
     * @param s some SCC in a symbolic execution graph.
     * @param render Flag indicating whether or not the SCC should be rendered.
     */
    public LLVMSCCProblem(SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> s, boolean render) {
        this("LLVM Symbolic Execution SCC", "New LLVM Symbolic Execution Graph SCC problem", s, render);
    }
    
    /**
     * @param s some SCC in a symbolic execution graph.
     * @param render Flag indicating whether or not the SCC should be rendered.
     */
    protected LLVMSCCProblem(String shortName, String longName, SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> s, boolean render) {
        super(shortName, longName);
        this.scc = s;
        this.renderSCC = render;
    }

    /**
     * Export our knowledge from the symbolic execution graph.
     * @param o export util
     * @return textual representation of the SE graph
     */
    @Override
    public String export(Export_Util eu) {
        return "SCC";
        //SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> exportGraph = new LLVMLassoGraph(getSCC());
        //return exportGraph.export("SCC of symbolic execution graph based on LLVM Program.", this.renderSCC, eu);
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Termination");
    }

    /**
     * @return the considered SCC.
     */
    public SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> getSCC() {
        return this.scc;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return null;
    }

}
