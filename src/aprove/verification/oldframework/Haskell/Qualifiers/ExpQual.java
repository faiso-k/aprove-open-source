package aprove.verification.oldframework.Haskell.Qualifiers;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * the expression qualifier is a bind parameter in do-structurs or a guard in list comprehension
 * exists only in the parser. it is later expanded to then's or a complex represenation of guards for lists
 */
public class ExpQual extends HaskellObject.HaskellObjectSkeleton implements HaskellQual {
    HaskellExp exp;

    public ExpQual(HaskellExp exp) {
         this.exp = exp;
    }

    public HaskellExp getExpression(){
         return this.exp;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new ExpQual(Copy.deep(this.getExpression())));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        this.exp = this.walk(this.exp,hv);
        return this;
    }

    @Override
    public HaskellExp toMonad(DoCompFactory fac,HaskellExp next){
        return fac.buildMonadThen(this.exp,next);
    }

    @Override
    public HaskellExp toListComp(DoCompFactory fac,HaskellExp next){
        return fac.buildListCompGuard(this.exp,next);
    }

}
