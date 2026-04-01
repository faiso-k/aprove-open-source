package aprove.prooftree.Export.ProofPurposeDescriptors;

import aprove.prooftree.Export.Utility.*;

public class MethodSummaryProofPurposeDescriptor extends ProofPurposeDescriptor {

    @Override
    public String export(Export_Util eu) {
        return "Computed Method Summary";
    }

    @Override
    public String getPurpose() {
        return "Method Summary";
    }

}
