package aprove.verification.theoremprover.Simplifier;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 *
 * @author Stephan Swiderski
 * @version $Id$
 */
public class ParameterEnlargementProof extends Proof {

    protected SimplifierObligation oldObl;
    protected SimplifierObligation newObl;
    protected Map parameterEnlargementInfo;

    public ParameterEnlargementProof(SimplifierObligation oldObl,Map parameterEnlargementInfo,SimplifierObligation newObl){
        super();
        this.parameterEnlargementInfo = parameterEnlargementInfo;
        this.oldObl = oldObl;
    this.newObl = newObl;
        this.name = "ParameterEnlargement";
        this.longName = "ParameterEnlargement";
        this.shortName = "PE";
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


        this.result.append("The following functions are enlarged:");
        this.result.append(o.linebreak());
        Iterator it = this.parameterEnlargementInfo.entrySet().iterator();
        while (it.hasNext()){
            Map.Entry e = (Map.Entry) it.next();
            SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol)e.getKey();
            Object[] fnsym_reps = (Object[])e.getValue();
            SyntacticFunctionSymbol fnsym = (SyntacticFunctionSymbol)fnsym_reps[0];
            Map reps = (Map)fnsym_reps[1];
            this.result.append("following terms in definition of "+o.math(o.export(fsym))+" are enlarged to Parameters in "+o.math(o.export(fnsym)));
            this.result.append(o.linebreak());
            Iterator it2 = reps.entrySet().iterator();
            while (it2.hasNext()){
               Map.Entry e2 = (Map.Entry) it2.next();
               AlgebraTerm t1 = (AlgebraTerm) e2.getKey();
               AlgebraTerm t2 = (AlgebraTerm) e2.getValue();
               this.result.append(t1+" "+t2);
               this.result.append(o.linebreak());
            }
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

