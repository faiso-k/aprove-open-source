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
public class ContextMoveProof extends Proof {

    protected SimplifierObligation oldObl;
    protected SimplifierObligation newObl;
    protected Map contextMoveInfo;

    public ContextMoveProof(SimplifierObligation oldObl,Map contextMoveInfo,SimplifierObligation newObl){
        super();
        this.contextMoveInfo = contextMoveInfo;
        this.oldObl = oldObl;
    this.newObl = newObl;
        this.name = "ContextMove";
        this.longName = "ContextMove";
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


        this.result.append("A context move was applied on following functions:");
        this.result.append(o.linebreak());
        this.result.append(o.linebreak());
        Iterator it = this.contextMoveInfo.entrySet().iterator();
        while (it.hasNext()){
            Map.Entry e = (Map.Entry) it.next();
            SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol)e.getKey();
            BitSet bset = (BitSet)e.getValue();
            this.result.append(o.indent(o.math(o.export(fsym)) +" at parameter(s) "+ bset));
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

