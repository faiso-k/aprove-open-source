package aprove.verification.theoremprover.TerminationProofs;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.SimplifierProblem.*;

/**
 * @author swiste
 * @version $Id$
 */
public class SimplifierProof extends Proof {
    SimplifierObligation oldObligation;
    SimplifierObligation newObligation;
    String msg;

    public SimplifierProof(SimplifierObligation moldObligation, SimplifierObligation mnewObligation, String msg,String name) {
        super();
        this.msg = msg;
    this.name = name;
        this.longName = name;
        this.shortName = name;
    this.oldObligation = moldObligation;
    this.newObligation = mnewObligation;
    }

    public SimplifierProof(SimplifierObligation moldObligation, SimplifierObligation mnewObligation, String name,String shortName,String longName,String msg) {
        super();
        this.msg = msg;
    this.name = name;
        this.longName = longName;
        this.shortName = shortName;
    this.oldObligation = moldObligation;
    this.newObligation = mnewObligation;
    };

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
