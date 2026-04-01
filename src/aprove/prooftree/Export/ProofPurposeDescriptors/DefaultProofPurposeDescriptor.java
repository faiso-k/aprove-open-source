package aprove.prooftree.Export.ProofPurposeDescriptors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;

public class DefaultProofPurposeDescriptor extends ProofPurposeDescriptor {

    private final BasicObligation obl;
    private final YNM status;
    private final String purpose;

    public DefaultProofPurposeDescriptor(BasicObligation obl, String purpose) {
        this.obl = obl;
        this.status = obl.getTruthValue().fallbackToYNM();
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
        sb.append(o.bold(this.purpose)+" of the given "+o.italic(this.obl.getName(NameLength.SHORT))+" could ");
        switch (this.status) {
        case YES : sb.append("be "+o.fontcolor("proven", color)+":");break;
        case NO  : sb.append("be "+o.fontcolor("disproven", color)+":");break;
        default  : sb.append("not be shown:");break;
        }
        sb.append(o.linebreak());
        sb.append(o.linebreak());
        return sb.toString();
    }

}
