/**
 *
 */
package aprove.verification.oldframework.Haskell.Evaluator;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;

public class RuleBlock {
    HaskellType type;
    List<HaskellRule> rules;
    int arity;
    HaskellSubstitution inSub;
    Var tyVar;

    public RuleBlock(Function func){
        this(func.getRules());
    }

    public RuleBlock(Var tyVar,HaskellType type){
        this.type = type;
        this.tyVar = tyVar;
        this.arity = 0;
    }

    public RuleBlock(Function func,HaskellType type,HaskellSubstitution inSub){
        this(func.getRules());
        this.type = type;
        this.inSub = inSub;
    }

    public RuleBlock(List<HaskellRule> rules){
        this(rules,rules.iterator().next().getTypeTerm(),rules.iterator().next().getPatterns().size(),null);
    }

    public RuleBlock(List<HaskellRule> rules,HaskellType type,int arity,HaskellSubstitution inSub){
        this.rules = rules;
        this.arity = arity;
        this.type = type;
        this.inSub = inSub;
    }

    /*
    public Substitution arityTypeMatch(int arity,HaskellType type){
        if (arity >= this.arity){
            Substitution res = BasicTerm.Tools.match(Copy.deep(this.type),type);
            if ((res != null) && (this.inSub != null)){
                res = inSub.combineWith(res);

                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    //System.out.println("ex");
                }

            }
            return res;

        }
        return null;
    }
    */

    /**
     * Tries to match this type to the given type. If this succeeds, then also
     * possible class instance substitutions are being accounted for and
     * integrated into the result.
     * @param type The type to match.
     * @return A substitution that matches this rule block to the given type,
     * or <code>null</code> if this rule block does not match.
     */
    public HaskellSubstitution fullClassTypeMatch(HaskellType type) {
        HaskellSubstitution res = BasicTerm.Tools.match(Copy.deep(this.type), type);
        if ( (res != null) && (this.inSub != null) ) {
            res = this.inSub.combineWith(res);
        }
        return res;
    }


    public int typeMatch(HaskellType type){
        HaskellSubstitution res = BasicTerm.Tools.match(Copy.deep(this.type),type);
        if (res != null){
            return this.arity;
        }
        return -1;
    }

    public int getArity(){
        return this.arity;
    }

    public List<HaskellRule> getRules(){
        return this.rules;
    }

    public Var getTypeVariable(){
        return this.tyVar;
    }
}