package aprove.prooftree.Export.ProofPurposeDescriptors;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.diophantine.*;
import aprove.verification.dpframework.*;

public class DiophantineProofPurposeDescriptor extends ProofPurposeDescriptor {

    private DiophantineConstraints diophantineConstraints;

    public DiophantineProofPurposeDescriptor(DiophantineConstraints diophantineConstraints) {
        this.diophantineConstraints = diophantineConstraints;
    }

    @Override
    public String getPurpose() {
        return null;
    }

    public String getName(NameLength length) {
        return "Diophantine Frame";
    }

    @Override
    public String export(Export_Util o) {
        return this.diophantineConstraints.export(o);
    }

}
