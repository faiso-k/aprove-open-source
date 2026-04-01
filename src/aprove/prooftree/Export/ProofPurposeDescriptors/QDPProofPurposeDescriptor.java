package aprove.prooftree.Export.ProofPurposeDescriptors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Logic.*;

/**
 * @author Matthias Sondermann
 * @version $Id$
 */

public class QDPProofPurposeDescriptor extends ProofPurposeDescriptor {

    private YNM status;
    private String purpose;

    public QDPProofPurposeDescriptor(QDPProblem qdpProblem) {
        super();
        this.status = (YNM)qdpProblem.getTruthValue();
        this.purpose = "Finiteness";
        // somewhat imprecise since "infiniteness" is not
        // the opposite of "finiteness"
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder sb = new StringBuilder();
        Color color = this.status.toColor();
        switch (this.status) {
            // Output is so complicated because YES and NO overlap,
            // cf. defs of "finiteness" and "infiniteness" of a DP problem
        case YES :
            sb.append(o.bold(this.purpose)+" of the given "+o.italic("QDPProblem")+" could ");
            sb.append("successfully be "+o.fontcolor("proven", color)+":");
            break;
        case NO  :
            sb.append(o.bold("Infiniteness")+" of the given "+o.italic("QDPProblem")+" could ");
            sb.append("successfully be "+o.fontcolor("proven", color)+":");
            break;
        default  :
            sb.append("Neither " + o.bold("finiteness")+ " nor " + o.bold("infiniteness"));
            sb.append(" of the given "+o.italic("QDPProblem")+" could be shown:");
            break;
        }
        sb.append(o.linebreak());
        sb.append(o.linebreak());
        //sb.append(this.trs.export(o));
        return sb.toString();
    }

    public String getName(NameLength length) {
        return "QDPProblem Frame";
    }

    @Override
    public String getPurpose() {
        return this.purpose;
    }

}
