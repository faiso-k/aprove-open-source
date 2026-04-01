package aprove.verification.theoremprover.TerminationProofs;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Input.*;

/**
 * This proof class collects and outputs parse errors.
 *
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public class CouldNotHandleSourceExceptionProof extends Proof {

    String msg;

    public CouldNotHandleSourceExceptionProof(String msg, Input input) {
        super();
    this.name = "Could not handle";
    this.shortName = "Could not handle";
    this.longName = "Could not handle";
        this.msg = msg;
    }

    @Override
    public String export(Export_Util o) {
        if (Proof.CACHE_VALUES) {
                if (this.result.length() != 0) {
                    return this.result.toString();
                }
        } else {
            this.startUp();
        }

        this.result.append(this.msg);
        this.result.append(o.cond_linebreak());
        return this.result.toString();
    }

    public String toBibTeX() {
        return "";
    }

}
