package aprove.verification.theoremprover.Simplifier;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 *
 * @author Stephan Swiderski
 * @version $Id$
 */
public class FixedValueProof extends Proof {

    protected SimplifierObligation oldObl;
    protected SimplifierObligation newObl;
    protected Vector<Rule> fixedValueInfo;

    public FixedValueProof(SimplifierObligation oldObl,Vector<Rule>  fixedValueInfo,SimplifierObligation newObl){
        super();
        this.fixedValueInfo = fixedValueInfo;
        this.oldObl = oldObl;
    this.newObl = newObl;
        this.name = "FixedValueTransformationm";
        this.longName = "FixedValueTransformation";
        this.shortName = "FVT";
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


        this.result.append("The following fixed value replacements are applied:");
        this.result.append(o.linebreak());
        this.result.append(o.set(this.fixedValueInfo,Export_Util.RULES));

        /*Iterator it = FixedValueInfo.entrySet().iterator();
        while (it.hasNext()){
            Map.Entry e = (Map.Entry) it.next();
            FunctionSymbol fsym = (FunctionSymbol)e.getKey();
            BitSet bset = (BitSet)e.getValue();
            this.result.append(fsym.getName() + bset);
            this.result.append(o.linebreak());
        }*/

/*        } else {
           this.result.append("Following function symbols could be marked as termianting:");
           this.result.append(o.linebreak());
           this.result.append(o.set(this.funcs,Export_Util.NICE_SET));
           this.result.append(o.linebreak());
        }*/
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

