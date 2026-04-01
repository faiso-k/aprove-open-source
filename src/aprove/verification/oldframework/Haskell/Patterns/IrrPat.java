package aprove.verification.oldframework.Haskell.Patterns;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 * XML-Bean
 * IrrPat represents the irrefutable Pattern (~) of haskell
 */
public class IrrPat extends HaskellPat.HaskellObjectSkeleton implements HaskellPat,HaskellBean {
    HaskellPat pattern;

    /**
     * do not use this constructor, its only for bean convention
     */
    public IrrPat(){
    }

    /**
     * normal constructor
     */
    public IrrPat(HaskellPat pattern){
        this.pattern = pattern;
    }

    public HaskellPat getPattern(){
        return this.pattern;
    }

    public void setPattern(HaskellPat pattern){
        this.pattern = pattern;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new IrrPat(Copy.deep(this.getPattern())));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseIrrPat(this);
        this.pattern = this.walk(this.pattern,hv);
        return hv.caseIrrPat(this);
    }


}
