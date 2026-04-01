package aprove.verification.oldframework.Haskell.Expressions;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * XML-Bean
 *
 * represents the stack of conditions of a rule
 */

public class CondStackExp extends HaskellObject.HaskellObjectSkeleton implements HaskellBean, HaskellExp {
      List <CondExp> conditions;

      /**
       * do not use this constructor, its only for bean convention
       */
      public CondStackExp(){
      }

      /**
       * normal constructor
       */
      public CondStackExp(List <CondExp> conditions){
          this.conditions = conditions;
      }

      public List<CondExp> getConditions(){
          return this.conditions;
      }

      public void setConditions(List<CondExp> conditions){
          this.conditions = conditions;
      }

      @Override
    public Object deepcopy(){
          return this.hoCopy(new CondStackExp(Copy.deepCol(this.getConditions())));
      }

      @Override
    public HaskellObject visit(HaskellVisitor hv){
          hv.fcaseCondStackExp(this);
          if (hv.guardCondStackConditions(this)) {
              this.conditions = this.listWalk(this.conditions,hv);
          }
          return hv.caseCondStackExp(this);
      }

}
