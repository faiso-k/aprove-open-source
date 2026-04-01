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
public class CaseMergeProof extends Proof {

    protected SimplifierObligation oldObl;
    protected SimplifierObligation newObl;
    protected Set<DefFunctionSymbol> cmInfo;

    public CaseMergeProof(SimplifierObligation oldObl,Set<DefFunctionSymbol> cmInfo,SimplifierObligation newObl){
        super();
        this.cmInfo = cmInfo;
        this.oldObl = oldObl;
    this.newObl = newObl;
        this.name = "CaseMerge";
        this.longName = "CaseMerge";
        this.shortName = "CM";
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


        this.result.append("Case Merge was applied to following functions :");
        this.result.append(o.linebreak());
        this.result.append(o.set(this.cmInfo,Export_Util.NICE_SET));
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

