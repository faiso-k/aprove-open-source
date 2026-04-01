package aprove.verification.oldframework.Haskell.BasicTerms;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * A BasicRule allows basic term rewriting with BasicTerms
 * it is used by the BasicRuleApplyVisitor
 */
public interface HaskellBasicRule extends HaskellObject {
    BasicTerm matchReplace(BasicTerm t);

    public static class HaskellBasicRuleSkeleton extends HaskellObject.Visitable implements HaskellBasicRule {
        BasicTerm left;
        BasicTerm right;

        public HaskellBasicRuleSkeleton(BasicTerm left,BasicTerm right){
            this.left = left;
            this.right = right;
        }

        @Override
        public Object deepcopy(){
            return new HaskellBasicRule.HaskellBasicRuleSkeleton(Copy.deep(this.left),Copy.deep(this.right));
        }

        @Override
        public HaskellObject visit(HaskellVisitor hv){
            this.left = this.walk(this.left,hv);
            this.right = this.walk(this.right,hv);
            return this;
        }

        /**
         * tries to apply the rule to term t at top level
         * if it is applicable the methode returns the new result
         * else null
         */
        @Override
        public BasicTerm matchReplace(BasicTerm t){
            HaskellSubstitution subs = BasicTerm.Tools.match(Copy.deep(this.left),t);
            if (subs == null) {
                return null;
            }
            BasicTerm bt = subs.applyTo(this.right);
        return bt;
        }

    }

}
