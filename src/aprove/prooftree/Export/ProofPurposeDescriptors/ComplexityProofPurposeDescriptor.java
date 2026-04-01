package aprove.prooftree.Export.ProofPurposeDescriptors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;

public class ComplexityProofPurposeDescriptor extends ProofPurposeDescriptor {

    private final BasicObligation obl;
    private final ComplexityYNM status;
    private final String purpose;

    public ComplexityProofPurposeDescriptor(BasicObligation obl, String purpose) {
        this.obl = obl;
        this.status = ComplexityYNM.toComplexityYNM(obl.getTruthValue());
        this.purpose = purpose;
    }

    @Override
    public String getPurpose() {
        return this.purpose;
    }

    public String getName(NameLength length) {
        return this.purpose + "-Frame";
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder sb = new StringBuilder();
        Color color = this.status.toColor();
        sb.append(o.escape("The " + this.purpose + " of the given "));
        sb.append(o.italic(this.obl.getName(NameLength.SHORT)));
        sb.append(o.escape(" could be proven to be "));
        sb.append(o.fontcolor(o.escape(this.status.toString()), color));
        sb.append(o.escape("."));
        sb.append(o.linebreak());
        sb.append(o.linebreak());
        return sb.toString();
    }

}
