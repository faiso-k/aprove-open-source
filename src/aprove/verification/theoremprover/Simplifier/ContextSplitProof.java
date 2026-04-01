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
public class ContextSplitProof extends Proof {

    protected SimplifierObligation oldObl;
    protected SimplifierObligation newObl;
    protected Vector contextSplitInfo;

    public ContextSplitProof(SimplifierObligation oldObl,Vector contextSplitInfo,SimplifierObligation newObl){
        super();
        this.contextSplitInfo = contextSplitInfo;
        this.oldObl = oldObl;
    this.newObl = newObl;
        this.name = "ContextSplit";
        this.longName = "ContextSplit";
        this.shortName = "CS";
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


        this.result.append("The following functions are split:");
        this.result.append(o.linebreak());
        Iterator it = this.contextSplitInfo.iterator();
        while (it.hasNext()){
            Object[] e = (Object[]) it.next();
            SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol)e[0];
            Integer pos = (Integer)e[1];
            SyntacticFunctionSymbol gsym = (SyntacticFunctionSymbol)e[2];
            this.result.append(o.math(o.export(fsym))+" is split in parameter "+pos+", added helper: "+o.math(o.export(gsym)));
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

