package aprove.verification.theoremprover.Simplifier;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 *
 * @author Stephan Swiderski
 * @version $Id$
 */
public class IdentityTransformationProof extends Proof {

    protected SimplifierObligation oldObl;
    protected SimplifierObligation newObl;
    protected Vector identityTransformationInfo;

    public IdentityTransformationProof(SimplifierObligation oldObl,Vector identityTransformationInfo,SimplifierObligation newObl){
        super();
        this.identityTransformationInfo = identityTransformationInfo;
        this.oldObl = oldObl;
    this.newObl = newObl;
        this.name = "IdentityTransformation";
        this.longName = "IdentityTransformation";
        this.shortName = "IT";
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


        this.result.append("Identity transformation applied on following functions:");
        this.result.append(o.linebreak());
        Iterator it = this.identityTransformationInfo.iterator();
        while (it.hasNext()){
            Object[] e = (Object[]) it.next();
            SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol)e[0];
            SyntacticFunctionSymbol gsym = (SyntacticFunctionSymbol)e[1];
            Rule rule = (Rule)e[2];
            this.result.append(o.math(o.export(fsym))+", projection rule:"+rule+", added helper: "+o.math(o.export(gsym)));
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

