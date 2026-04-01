package aprove.prooftree.Export.ProofPurposeDescriptors;

import aprove.input.Programs.prolog.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;

/**
 * Created on 03.01.2006 by nowonder
 * @author nowonder, cryingshadow
 * @version $Id$
 */
public class PrologProofPurposeDescriptor extends ProofPurposeDescriptor {

    private final PrologProblem pp;
    //private final TruthValue status;

    public PrologProofPurposeDescriptor(PrologProblem obl/*, String p*/) {
        super();
        this.pp = obl;
        this.setStatus(obl.getTruthValue());
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder object = new StringBuilder();
        object.append("the query pattern");
        object.append(o.newline());
        object.append(this.pp.getQuery().export(o));
        object.append(o.newline());
        object.append("w.r.t. the given ");
        object.append(o.italic("Prolog program"));
        return
            ProofPurposeDescriptor.export(
                this.getStatus(),
                this.pp.getQuery().getPurpose().toString(),
                object.toString(),
                o
            );
    }

    public String getName(NameLength length) {
        return this.getPurpose() + " Frame";
    }

    @Override
    public String getPurpose() {
        return this.pp.getQuery().getPurpose().toString();
    }

}
