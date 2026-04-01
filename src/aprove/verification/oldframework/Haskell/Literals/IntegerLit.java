package aprove.verification.oldframework.Haskell.Literals;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Patterns.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This class represents an integer literal of Haskell.
 */

public class IntegerLit extends HaskellPat.HaskellObjectSkeleton implements HaskellBean, HaskellLit {
    int intValue;

    public IntegerLit(){
    }

    public IntegerLit(int intValue){
        this.intValue = intValue;
    }

    public void negate(){
        this.intValue = -this.intValue;
    }

    public int getIntValue(){
        return this.intValue;
    }

    public void setIntValue(int intValue){
        this.intValue = intValue;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new IntegerLit(this.getIntValue()));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        return hv.caseIntegerLit(this);
    }

}
