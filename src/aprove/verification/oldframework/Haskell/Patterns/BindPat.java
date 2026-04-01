package aprove.verification.oldframework.Haskell.Patterns;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * Haskell Variable binding pattern .i.e this term:  variable@subPattern
 * XML-Bean;
 */

public class BindPat extends HaskellObject.HaskellObjectSkeleton implements HaskellBean, HaskellPat {
    HaskellPat subPattern;
    Var variable;

    /**
     * do not use this constructor, its only for bean convention
     */
    public BindPat(){
    }

    /**
     * normal constructor
     */
    public BindPat(Var variable,HaskellPat subPattern){
        this.subPattern = subPattern;
        this.variable = variable;
    }

    public Var getVariable(){
        return this.variable;
    }

    public void setVariable(Var variable){
        this.variable = variable;
    }

    public HaskellPat getSubPattern(){
        return this.subPattern;
    }

    public void setSubPattern(HaskellPat subPattern){
        this.subPattern = subPattern;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new BindPat(Copy.deep(this.getVariable()),Copy.deep(this.getSubPattern())));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        if (hv.guardBindPat(this)) {
            this.subPattern = this.walk(this.subPattern,hv);
            this.variable = this.walk(this.variable,hv);
        }
        return hv.caseBindPat(this);
    }

    @Override
    public String toString(){
        return this.variable+"@"+this.subPattern;
    }

}
