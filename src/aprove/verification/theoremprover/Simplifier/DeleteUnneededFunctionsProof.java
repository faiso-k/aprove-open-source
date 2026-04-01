package aprove.verification.theoremprover.Simplifier;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 *
 * @author Stephan Swiderski
 * @version $Id$
 */
public class DeleteUnneededFunctionsProof extends Proof {

    protected SimplifierObligation oldObl;
    protected SimplifierObligation newObl;
    protected Set deleteUnneededFunctionsInfo;

    public DeleteUnneededFunctionsProof(SimplifierObligation oldObl,Set deleteUnneededFunctionsInfo,SimplifierObligation newObl){
        super();
        this.deleteUnneededFunctionsInfo = deleteUnneededFunctionsInfo;
        this.oldObl = oldObl;
    this.newObl = newObl;
        this.name = "DeleteUnneededFunctions";
        this.longName = "DeleteUnneededFunctions";
        this.shortName = "DUF";
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


        this.result.append("The following functions are removed:");
        this.result.append(o.linebreak());
        this.result.append(o.set(this.deleteUnneededFunctionsInfo,Export_Util.NICE_SET));
        this.result.append(o.linebreak());
        return this.result.toString();
    }

    @Override
    public String toHTML(){
       return this.export(new HTML_Util());
    }

    /**
     * Returns a LaTeX representation of the result.
     */
    @Override
    public String toLaTeX(){
        return this.export(new LaTeX_Util());
    }



}

