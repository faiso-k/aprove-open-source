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
public class SymbolicProof extends Proof {

    protected SimplifierObligation oldObl;
    protected SimplifierObligation newObl;
    protected Vector<DefFunctionSymbol> symbolicInfo;

    public SymbolicProof(SimplifierObligation oldObl,Vector<DefFunctionSymbol>  symbolicInfo,SimplifierObligation newObl){
        super();
        this.symbolicInfo = symbolicInfo;
        this.oldObl = oldObl;
    this.newObl = newObl;
        this.name = "SymbolicEvaluation";
        this.longName = "SymbolicEvaluation";
        this.shortName = "SE";
    }


    public SimplifierObligation getOriginalObligation() {
    return this.oldObl;
    }

    public SimplifierObligation getNewObligation() {
        return this.newObl;
    }

    public Collection getNewObligations() {
        return null;
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


        this.result.append("Symbolic Evaluation was applied to following functions:");
        this.result.append(o.linebreak());
        this.result.append(o.set(this.symbolicInfo,Export_Util.NICE_SET));

        /*Iterator it = SymbolicInfo.entrySet().iterator();
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

    public String toBibTeX() {
    return "";
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

