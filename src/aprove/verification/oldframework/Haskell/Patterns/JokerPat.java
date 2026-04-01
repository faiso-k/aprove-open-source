package aprove.verification.oldframework.Haskell.Patterns;

import aprove.verification.oldframework.Haskell.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 * JokerPat represents the Joker pattern (_) in Haskell
 */
public class JokerPat extends HaskellObject.HaskellObjectSkeleton implements HaskellPat,HaskellBean {
    @Override
    public Object deepcopy(){
        return this.hoCopy(new JokerPat());
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        return hv.caseJokerPat(this);
    }

    @Override
    public String toString(){
        return "_";
    }
}
