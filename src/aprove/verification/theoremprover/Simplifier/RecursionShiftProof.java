package aprove.verification.theoremprover.Simplifier;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 *
 * @author Stephan Swiderski
 * @version $Id$
 */
public class RecursionShiftProof extends Proof {

    protected SimplifierObligation oldObl;
    protected SimplifierObligation newObl;
    protected Set<DefFunctionSymbol> rsInfo;

    public RecursionShiftProof(SimplifierObligation oldObl,Set<DefFunctionSymbol> rsInfo,SimplifierObligation newObl){
        super();
        this.rsInfo = rsInfo;
        this.oldObl = oldObl;
    this.newObl = newObl;
        this.name = "RecursionShift";
        this.longName = "RecursionShift";
        this.shortName = "RS";
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


        this.result.append("Recursion Shifting was applied to following functions :");
        this.result.append(o.linebreak());
        this.result.append(o.set(this.rsInfo,Export_Util.NICE_SET));
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

