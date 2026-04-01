package aprove.verification.complexity.LowerBounds;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.Util.Renaming.*;


public class CpxTrsLowerBoundsProblem extends DefaultBasicObligation {

    private LowerBoundsTrs trs;
    private RenamingCentral renamingCentral;

    public CpxTrsLowerBoundsProblem(LowerBoundsTrs trs, RenamingCentral renamingCentral) {
        super("typed CpxTrs", "typed Term Rewrite System for analysis of lower complexity bounds");
        this.trs = trs;
        this.renamingCentral = renamingCentral;
    }

    @Override
    public String getStrategyName() {
        return "cpxlowerbounds";
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new ComplexityProofPurposeDescriptor(this, "Lowerbounds for Runtime Complexity (innermost)");
    }

    @Override
    public String export(Export_Util eu) {
        return this.trs.export(eu);
    }

    public LowerBoundsTrs getTrs() {
        return this.trs;
    }

    public RenamingCentral getRenamingCentral() {
        return this.renamingCentral;
    }

}
