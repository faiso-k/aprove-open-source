package aprove.verification.oldframework.Haskell.Substitutors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This Visitor applies a set of BasicRule to a term.
 * Each subterm of a HaskellObject is check if it matches to
 * a left hand side of a rule out of the set.
 * If it matches, the subterm is replaced by the right hand side.
 * The visitor does not visit a replaced subterm.
 * It does not stop after one replacement.
 */
public class BasicRuleApplyVisitor extends HaskellVisitor {
     Set<HaskellBasicRule> rules;
     boolean active;

     public BasicRuleApplyVisitor(Set<HaskellBasicRule> rules){
         this.rules = rules;
         this.active = false;
     }

     @Override
    public HaskellObject caseCons(Cons ho){
         return this.applyRules(ho);
     }

     @Override
    public HaskellObject caseApply(Apply ho){
         return this.applyRules(ho);
     }

     public HaskellObject applyRules(BasicTerm bt){
         for (HaskellBasicRule rule : this.rules){
             BasicTerm nbt = rule.matchReplace(bt);
             if (nbt != null) {
                this.active = true;
                return nbt;
             }
         }
         return bt;
     }


     /**
      * returns true if this visitor has applied a rule,
      * and resets the active flag
      */
     public boolean wasActive(){
         boolean a = this.active;
         this.active = false;
         return a;
     }


}