package aprove.verification.oldframework.Haskell.Patterns;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Literals.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 * PlusPat is the Plus-pattern (x+n) of Haskell (n is an integer literal)
 */
public class PlusPat extends HaskellPat.HaskellObjectSkeleton implements HaskellPat,HaskellBean {
    Var variable;
    IntegerLit integer;

    /**
     * do not use this constructor, its only for bean convention
     */
    public PlusPat(){
    }

    /**
     * normal constructor
     */
    public PlusPat(Var variable,IntegerLit integer){
        this.variable = variable;
        this.integer = integer;
    }

    public IntegerLit getInteger(){
        return this.integer;
    }

    public void setInteger(IntegerLit integer){
        this.integer = integer;
    }

    public Var getVariable(){
        return this.variable;
    }

    public void setVariable(Var variable){
        this.variable = variable;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new PlusPat(Copy.deep(this.getVariable()),Copy.deep(this.getInteger())));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        if (hv.guardPlusPat(this)) {
            this.variable = this.walk(this.variable,hv);
            this.integer = this.walk(this.integer,hv);
        }
        return hv.casePlusPat(this);
    }

}
