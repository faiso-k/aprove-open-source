package aprove.verification.oldframework.Haskell.Qualifiers;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
   the generator qualifier is a bind parameter in do-structurs or the generator in list comprehension
* exists only in the parser. it is later expanded to its basic representation
*/
public class GenQual extends HaskellObject.HaskellObjectSkeleton implements HaskellQual {
    HaskellPat pat;
    HaskellExp exp;

    public GenQual(HaskellPat pat,HaskellExp exp) {
         this.pat = pat;
         this.exp = exp;
    }

    public HaskellExp getExpression(){
         return this.exp;
    }

    public HaskellPat getPattern(){
         return this.pat;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new GenQual(Copy.deep(this.pat),Copy.deep(this.exp)));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        this.pat = this.walk(this.pat,hv);
        this.exp = this.walk(this.exp,hv);
        return this;
    }

    @Override
    public HaskellExp toMonad(DoCompFactory fac,HaskellExp next){
        return fac.buildMonadBind(this.pat,this.exp,next);
    }

    @Override
    public HaskellExp toListComp(DoCompFactory fac,HaskellExp next){
        return fac.buildListCompGen(this.pat,this.exp,next);
    }

}
