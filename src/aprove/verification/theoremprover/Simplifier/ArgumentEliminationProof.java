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
public class ArgumentEliminationProof extends Proof {

    protected SimplifierObligation oldObl;
    protected SimplifierObligation newObl;
    protected Vector<Rule> afs;

    public ArgumentEliminationProof(SimplifierObligation oldObl,Vector<Rule> afs,SimplifierObligation newObl){
        super();
        this.afs = afs;
        this.oldObl = oldObl;
    this.newObl = newObl;
        this.name = "ArgumentElimination";
        this.longName = "ArgumentElimination";
        this.shortName = "AE";
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


        this.result.append("The following argument filtering was applied:");
        this.result.append(o.linebreak());
        this.result.append(o.set(this.afs,Export_Util.RULES));
        /*Iterator it = afs.entrySet().iterator();
        while (it.hasNext()){
            Map.Entry e = (Map.Entry) it.next();
            FunctionSymbol fsym = (FunctionSymbol) e.getKey();
            BigInteger af = (BigInteger)e.getValue();
            this.result.append(fsym+" -- "+af);
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

