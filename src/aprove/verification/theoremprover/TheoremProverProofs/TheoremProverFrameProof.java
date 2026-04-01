/*
 * Created on 09.07.2004
 *
 */
package aprove.verification.theoremprover.TheoremProverProofs;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.TheoremProverProblem.*;

/**
 * @author rabe
 *
 */
public class TheoremProverFrameProof extends ProofPurposeDescriptor {

    private YNM                     status;
    private String                     purpose;
    private TheoremProverObligation theoremProverObligation;

    public TheoremProverFrameProof(TheoremProverObligation theoremProverObligation) {
        this.purpose = "Partial correctness";
        this.status = (YNM)theoremProverObligation.getTruthValue();
        this.theoremProverObligation = theoremProverObligation;
    }


    /**
     *
     */
    @Override
    public String export(Export_Util o) {
        StringBuilder sb = new StringBuilder();
        Color color = this.status.toColor();
        sb.append(o.bold(this.purpose)+" of the following Program");
        sb.append(o.linebreak());
        sb.append(o.linebreak());
        sb.append(this.theoremProverObligation.getProgram().export(o));
        sb.append(o.linebreak());
        sb.append(o.bold("using the following formula:"));
        sb.append(o.linebreak());
        sb.append(o.export(this.theoremProverObligation.getFormula()));
        sb.append(o.linebreak());
        sb.append(o.linebreak());
        switch (this.status) {
            case YES : sb.append("could be successfully "+o.fontcolor("shown", color)+":");break;
            case NO  : sb.append("could be successfully "+o.fontcolor("disproved", color)+":");break;
            default  : sb.append("could not be shown:");break;
        }
        sb.append(o.linebreak());

        return sb.toString();
    }

    @Override
    public String getPurpose() {
        return this.purpose;
    }

    public String getName(NameLength length) {
        return "Induction Frame Proof";
    }

}

