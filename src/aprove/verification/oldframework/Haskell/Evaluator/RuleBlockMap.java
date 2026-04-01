/**
 *
 */
package aprove.verification.oldframework.Haskell.Evaluator;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class RuleBlockMap extends HashMap<HaskellEntity,List<RuleBlock>> {
    HaskellEntity errorEntity;
    HaskellEntity termiEntity;
    Pair<RuleBlock,HaskellSubstitution> termiPair;

    private final Pair<RuleBlock,HaskellSubstitution> insufficientArgumentsPair;

    public RuleBlockMap(HaskellEntity errorEntity,HaskellEntity termiEntity,Pair<RuleBlock,HaskellSubstitution> termiPair, Pair<RuleBlock,HaskellSubstitution> insufficientArgumentsPair) {
        super();
        this.errorEntity = errorEntity;
        this.termiEntity = termiEntity;
        this.termiPair = termiPair;
        this.insufficientArgumentsPair = insufficientArgumentsPair;
    }

    public Pair<RuleBlock,HaskellSubstitution> getRuleBlock(int arity,HaskellEntity ve,HaskellType type){
        if (ve == this.errorEntity) {
            return null;
        }
        if (ve == this.termiEntity) {
            return this.termiPair;
        }
        List<RuleBlock> ruleBlocks = this.get(ve);
        if (ruleBlocks == null) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println(ve+"  ::  "+type+"  |  "+arity);
            }
            if (ve instanceof CVarEntity) {
                MemberTypeSchema mts = (MemberTypeSchema)ve.getType();
                ClassConstraint cc = mts.getClassConstraint();
                RuleBlock rb = new RuleBlock((Var)cc.getType(),mts.getMatrix());
                // the arity of the newly created rule block does not have to be checked,
                // since it is always 0 for a class rule block (cf. the above used constructor)
                HaskellSubstitution tsubs = rb.fullClassTypeMatch(type);
                if (tsubs != null) {
                    return new Pair<RuleBlock,HaskellSubstitution>(rb,tsubs);
                }
            }
            throw new RuntimeException("no RuleBlocks for non CVar");
        }
        for (RuleBlock rb: ruleBlocks){
            //Substitution tsubs = rb.arityTypeMatch(arity,type);
            HaskellSubstitution tsubs = rb.fullClassTypeMatch(type);
            if (tsubs != null) {
                if (arity >= rb.arity) {
                    return new Pair<RuleBlock,HaskellSubstitution>(rb,tsubs);
                }
                else {
                    // the type is being matched, but the arity is insufficient
                    return this.insufficientArgumentsPair;
                }
            }
        }
        return null;
    }

    public boolean hasCorrectArity(int arity,HaskellEntity ve,HaskellType type){
        List<RuleBlock> ruleBlocks = this.get(ve);
        if (ruleBlocks == null) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println(ve+"  ::  "+type+"  |  "+arity);
            }
        }
        boolean res = true;
        for (RuleBlock rb: ruleBlocks){
            int i = rb.typeMatch(type);
            if (i > -1) {
                if (i <= arity) {
                    return true;
                }
                res = false;
            }
        }
        return res;
    }

    public void addRuleBlock(HaskellEntity ve,RuleBlock rb){
        List<RuleBlock> ruleBlocks = this.get(ve);
        if (ruleBlocks == null) {
            ruleBlocks = new Vector<RuleBlock>();
            this.put(ve,ruleBlocks);
        }
        ruleBlocks.add(rb);
    }

}