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
public class FunctionMergeProof extends Proof {

    protected SimplifierObligation oldObl;
    protected SimplifierObligation newObl;
    protected Map functionMergeInfo;

    public FunctionMergeProof(SimplifierObligation oldObl,Map functionMergeInfo,SimplifierObligation newObl){
        super();
        this.functionMergeInfo = functionMergeInfo;
        this.oldObl = oldObl;
    this.newObl = newObl;
        this.name = "FunctionMerge";
        this.longName = "FunctionMerge";
        this.shortName = "FM";
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


        this.result.append("The following functions are merged:");
        this.result.append(o.linebreak());
        Iterator it = this.functionMergeInfo.entrySet().iterator();
        while (it.hasNext()){
            Map.Entry e = (Map.Entry) it.next();
            SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol)e.getKey();
            SyntacticFunctionSymbol gsym = (SyntacticFunctionSymbol)e.getValue();
            this.result.append(o.math(o.export(gsym))+" is merged into "+o.math(o.export(fsym)));
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

