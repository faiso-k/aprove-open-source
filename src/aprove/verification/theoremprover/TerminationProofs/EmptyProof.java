package aprove.verification.theoremprover.TerminationProofs;

import aprove.prooftree.Export.Utility.*;

/**
 * This class represents a dummy proof with just a text message.
 * If you dare use it without specifying the origin and new obligation,
 * it will utterly destroy all the rest of the proof tree
 *
 * @author Peter Schneider-Kamp, Christian Kaeunicke
 * @version $Id$
 */
public class EmptyProof extends Proof {
    String msg;

    public EmptyProof(String msg) {
        super();
        this.msg = msg;
        this.name = "Empty";
        this.shortName = "Empty";
        this.longName = "Empty";
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
        return this.msg;
    }

}
