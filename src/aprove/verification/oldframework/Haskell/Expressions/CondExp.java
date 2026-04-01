package aprove.verification.oldframework.Haskell.Expressions;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * XML-Bean
 *
 * represents a condition expression (guarded expression) in rule
 */
public class CondExp extends HaskellObject.HaskellObjectSkeleton implements HaskellBean, HaskellExp {
      HaskellExp condition;
      HaskellExp result;

      /**
       * do not use this constructor, its only for bean convention
       */
      public CondExp(){
      }

      /**
       * normal constructor
       */
      public CondExp(HaskellExp condition,HaskellExp result){
          this.condition = condition;
          this.result = result;
      }

      public HaskellExp getCondition(){
          return this.condition;
      }

      public void setCondition(HaskellExp condition){
          this.condition = condition;
      }

      public HaskellExp getResult(){
          return this.result;
      }

      public void setResult(HaskellExp result){
          this.result = result;
      }

      @Override
    public Object deepcopy(){
          return this.hoCopy(new CondExp(Copy.deep(this.getCondition()),Copy.deep(this.getResult())));
      }

      @Override
    public HaskellObject visit(HaskellVisitor hv){
          this.condition = this.walk(this.condition,hv);
          this.result = this.walk(this.result,hv);
          return hv.caseCondExp(this);
      }

}
