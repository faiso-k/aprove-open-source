package aprove.verification.oldframework.Haskell.Expressions;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The LambdaExp reprresents the Lambda terms in Haskell, it contains
 * the patterns, the result expression and the local variables in an entityframe
 *
 * XML-Bean
 *
 */
public class LambdaExp extends HaskellObject.HaskellObjectSkeleton implements HaskellBean, HaskellExp, RightTypeBinding, EntityFrameCarrier {
    List<HaskellPat> patterns;
    HaskellExp result;
    EntityFrame entityFrame;

    /**
     * do not use this constructor, its only for bean convention
     */
    public LambdaExp(){
    }

    /**
     * constructor for deepcopy
     */
    public LambdaExp(List<HaskellPat> patterns,HaskellExp result,EntityFrame entityFrame) {
         this.patterns = patterns;
         this.result = result;
         this.entityFrame = entityFrame;
    }

    /**
     * normal constructor
     */
    public LambdaExp(List<HaskellPat> patterns,HaskellExp result) {
         this(patterns,result,null);
    }

    public void setResult(HaskellExp result){
         this.result = result;
    }

    public HaskellExp getResult(){
         return this.result;
    }

    public void setPatterns(List<HaskellPat> patterns){
         this.patterns = patterns;
    }

    public List<HaskellPat> getPatterns(){
         return this.patterns;
    }

    @Override
    public Object deepcopy(){
         return this.hoCopy(new LambdaExp(Copy.deepCol(this.patterns),Copy.deep(this.getResult()),this.entityFrame));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseEntityFrame(this.entityFrame);
        hv.fcaseLambdaExp(this);
        this.patterns = this.listWalk(this.patterns,hv);
        hv.icaseLambdaExp(this);
        this.result = this.walk(this.result,hv);
        hv.icaseEntityFrame(this.entityFrame);
        if (hv.guardLambdaExpEntityFrame(this)){
            this.entityFrame = this.walk(this.entityFrame,hv);
        }
        return hv.caseLambdaExp(this);
    }

    /**
     * the type is shifted down to the result RawTerm
     * i.e.: <code> f . \x -> 5 :: Int  </code><br/>
     * is transformed to <code> f . \x -> (5 :: Int)  </code><br/>
     * cause of ugly haskell syntax.
     */
    @Override
    public void shiftTypeDown(HaskellPreType type){
        RawTerm rt = (RawTerm) this.result;
        rt.shiftTypeDown(type);
    }

    @Override
    public void setEntityFrame(EntityFrame entityFrame){
        this.entityFrame = entityFrame;
    }

    @Override
    public EntityFrame getEntityFrame(){
        return this.entityFrame;
    }

}
