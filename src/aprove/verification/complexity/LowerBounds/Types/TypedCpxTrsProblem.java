package aprove.verification.complexity.LowerBounds.Types;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;

public class TypedCpxTrsProblem extends DefaultBasicObligation {

    private TypedTrs trs;

    public TypedCpxTrsProblem(TypedTrs trs) {
        super("typed CpxTrs", "typed Term Rewrite System for complexity analysis");
        this.trs = trs;
    }

    public TypedTrs getTrs() {
        return this.trs;
    }

    @Override
    public String getStrategyName() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new ComplexityProofPurposeDescriptor(this, "Runtime Complexity (innermost)");
    }

    @Override
    public String export(Export_Util eu) {
        return this.trs.export(eu);
    }

}
