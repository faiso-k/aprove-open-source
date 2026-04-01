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
public class SynonymProof extends Proof {

    protected SimplifierObligation oldObl;
    protected SimplifierObligation newObl;
    protected Map synonymInfo;

    public SynonymProof(SimplifierObligation oldObl,Map synonymInfo,SimplifierObligation newObl){
        super();
        this.synonymInfo = synonymInfo;
        this.oldObl = oldObl;
    this.newObl = newObl;
        this.name = "SynonymTransformation";
        this.longName = "SynonymTransformation";
        this.shortName = "ST";
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


        this.result.append("The following functions are synonyms:");
        this.result.append(o.linebreak());
        Iterator it = this.synonymInfo.entrySet().iterator();
        while (it.hasNext()){
            Map.Entry e = (Map.Entry) it.next();
            SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol)e.getKey();
            SyntacticFunctionSymbol gsym = (SyntacticFunctionSymbol)e.getValue();
            this.result.append(o.math(o.export(fsym)+"="+o.export(gsym)));
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

