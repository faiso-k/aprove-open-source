package aprove.verification.oldframework.Haskell.Literals;

import java.math.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Patterns.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This class represents the float literal of Haskell
 */
public class FloatLit extends HaskellPat.HaskellObjectSkeleton implements HaskellLit {
    BigDecimal floatValue;

    public FloatLit(){
    }

    public FloatLit(BigDecimal floatValue){
        this.floatValue = floatValue;
    }

    public void negate(){
        this.floatValue = this.floatValue.negate();
    }

    public BigDecimal getFloatValue(){
        return this.floatValue;
    }

    public void setFloatValue(BigDecimal floatValue){
        this.floatValue = floatValue;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new FloatLit(this.getFloatValue()));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        return hv.caseFloatLit(this);
    }

}
