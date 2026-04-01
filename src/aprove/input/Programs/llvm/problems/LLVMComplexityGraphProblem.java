package aprove.input.Programs.llvm.problems;

import aprove.input.Programs.llvm.segraph.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;

/**
 * A symbolic execution graph generated from some LLVM program and a start function.
 * @author Marc Brockschmidt
 */
public class LLVMComplexityGraphProblem extends LLVMSEGraphProblem {

    /**
     * @param graphParam a graph created by symbolic evaluation of some program.
     * @param renderGraphParam Flag indicating whether or not the graph should be rendered.
     */
    public LLVMComplexityGraphProblem(final LLVMSEGraph graphParam, final boolean renderGraphParam) {
        super(graphParam, renderGraphParam);
    }

    /**
     * Export our knowledge from the termination graph.
     * @param o export util
     * @return textual representation of the FI graph
     */
    @Override
    public String export(Export_Util eu) {
        return "Complexity-Graph";
        //return this.graph.export("Symbolic Execution Graph based on LLVM Program:", this.renderGraph, eu);
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Complexity");
    }

}
