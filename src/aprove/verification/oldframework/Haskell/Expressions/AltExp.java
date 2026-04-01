package aprove.verification.oldframework.Haskell.Expressions;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 * XML-Bean
 * represents one case alternative of an case expression
 * conatins the pattern, the expression and an entityFrame for the varentities in the pattern
 */

public class AltExp extends HaskellObject.HaskellObjectSkeleton implements HaskellBean, HaskellExp, EntityFrameCarrier {
     HaskellPat pattern;
     HaskellExp expression;
     EntityFrame entityFrame;

    /**
     * do not use this constructor, its only for bean convention
     */
     public AltExp(){
     }

     /**
      * constructor for deepcopy
      */
     public AltExp(HaskellPat pattern,HaskellExp expression, EntityFrame entityFrame){
         this.pattern = pattern;
         this.expression = expression;
         this.entityFrame = entityFrame;
     }

     /**
      * normal constructor
      */
     public AltExp(HaskellPat pattern,HaskellExp expression){
         this(pattern,expression,null);
     }

     public HaskellPat getPattern(){
         return this.pattern;
     }

     public void setPattern(HaskellPat pattern){
         this.pattern = pattern;
     }

     public HaskellExp getExpression(){
         return this.expression;
     }

     public void setExpression(HaskellExp expression){
         this.expression = expression;
     }

     @Override
    public Object deepcopy(){
        return this.hoCopy(new AltExp(Copy.deep(this.pattern),Copy.deep(this.expression),this.entityFrame));
     }

     @Override
    public HaskellObject visit(HaskellVisitor hv){
         hv.fcaseEntityFrame(this.entityFrame);
         hv.fcaseAltExp(this);
         this.pattern = this.walk(this.pattern,hv);
         hv.icaseAltExp(this);
         this.expression = this.walk(this.expression,hv);
         hv.icaseEntityFrame(this.entityFrame);
         if (hv.guardAltExpEntityFrame(this)){
            this.entityFrame = this.walk(this.entityFrame,hv);
         }
         return hv.caseAltExp(this);
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
