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
public class FunctionCombinationProof extends Proof {

    protected SimplifierObligation oldObl;
    protected SimplifierObligation newObl;
    protected Vector combineInfo;

    public FunctionCombinationProof(SimplifierObligation oldObl,Vector combineInfo,SimplifierObligation newObl){
        super();
        this.combineInfo = combineInfo;
        this.oldObl = oldObl;
    this.newObl = newObl;
        this.name = "FunctionCombination";
        this.longName = "FunctionCombination";
        this.shortName = "FC";
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


        this.result.append("The following functions are combined:");
        this.result.append(o.linebreak());
        Iterator it = this.combineInfo.iterator();
        while (it.hasNext()){
            Vector<DefFunctionSymbol> vodfs = (Vector<DefFunctionSymbol>) it.next();
            Vector<DefFunctionSymbol> v = new Vector<DefFunctionSymbol>(vodfs);
            DefFunctionSymbol df = (DefFunctionSymbol) v.remove(0);
            this.result.append(o.set(v,Export_Util.NICE_SET));
            this.result.append(o.rightarrow());
            this.result.append(o.export(df));
            this.result.append(o.linebreak());
        }

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

