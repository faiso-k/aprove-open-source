package aprove.verification.oldframework.Haskell.Expressions;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The IFexp represents the If-Expression in Haskell,
 * it contains the condition and both cases.
 * XML-Bean
 */

public class IfExp extends HaskellObject.HaskellObjectSkeleton implements HaskellBean, HaskellExp, RightTypeBinding  {
    HaskellExp cond;
    HaskellExp trueCase;
    HaskellExp falseCase;

    /**
     * do not use this constructor, its only for bean convention
     */
    public IfExp(){
    }

    /**
     * normal constructor
     */
    public IfExp(HaskellExp cond,HaskellExp trueCase,HaskellExp falseCase) {
       this.cond = cond;
       this.trueCase = trueCase;
       this.falseCase = falseCase;
    }

    public HaskellExp getCond(){
       return this.cond;
    }

    public void setCond(HaskellExp cond){
       this.cond = cond;
    }

    public HaskellExp getTrueCase(){
       return this.trueCase;
    }

    public void setTrueCase(HaskellExp trueCase){
       this.trueCase = trueCase;
    }

    public HaskellExp getFalseCase(){
       return this.falseCase;
    }

    public void setFalseCase(HaskellExp falseCase){
       this.falseCase = falseCase;
    }

    @Override
    public Object deepcopy(){
       return this.hoCopy(new IfExp(Copy.deep(this.getCond()),Copy.deep(this.getTrueCase()),Copy.deep(this.getFalseCase())));
    }

    /**
     * the type is shifted down to the result RawTerm
     * i.e.: <code> f . if (..) then  5 else 1 :: Int  </code><br/>
     * is transformed to <code> if (..) then 5 else (1 :: Int)  </code><br/>
     * cause of ugly haskell syntax.
     */
    @Override
    public void shiftTypeDown(HaskellPreType type){
        RawTerm rt = (RawTerm) this.falseCase;
        rt.shiftTypeDown(type);
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseIfExp(this);
        this.cond = this.walk(this.cond,hv);
        hv.icaseIfExp(this);
        this.trueCase = this.walk(this.trueCase,hv);
        hv.iicaseIfExp(this);
        this.falseCase = this.walk(this.falseCase,hv);
        return hv.caseIfExp(this);
    }


}
