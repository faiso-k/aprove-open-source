/**
 *
 */
package aprove.verification.oldframework.Haskell.Narrowing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class InstanceCombinator implements Collection_Util.Combinator<Triple<HaskellSubstitution,HaskellSubstitution,HaskellExp>>{
    HaskellExp baseReplace;
    List<Var> vars;
    HaskellSubstitution ptySubs;
    HaskellSubstitution psubs;
    HaskellSubstitution tyMatchSubs;

    public InstanceCombinator(HaskellExp baseReplace,List<Var> vars,HaskellSubstitution ptySubs,HaskellSubstitution psubs,HaskellSubstitution tyMatchSubs){
        this.baseReplace = baseReplace;
        this.vars = vars;
        this.ptySubs = ptySubs;
        this.psubs = psubs;
        this.tyMatchSubs = tyMatchSubs;
    }

    @Override
    public Triple<HaskellSubstitution,HaskellSubstitution,HaskellExp> combine(Object[] objs){
        int i = 0;
        HaskellSubstitution subs = this.psubs;;
        HaskellSubstitution tySubs = this.ptySubs;;
        HaskellSubstitution instance = new HaskellSubstitution();
        for (Var var : this.vars){
            Triple triple = (Triple) objs[i];
            tySubs = tySubs.combineWith((HaskellSubstitution) triple.x);
            subs = subs.combineWith((HaskellSubstitution) triple.y);
            HaskellExp exp = (HaskellExp) triple.z;
            i++;
            instance.put(var.getSymbol(),exp);
        }
        BasicTerm res = Copy.deep((BasicTerm)this.baseReplace);
        (new TypeAnnotationSubstitutor(this.tyMatchSubs)).applyTo(res);
        res = instance.applyTo(res);
        res = subs.applyTo(res);
        (new TypeAnnotationSubstitutor(tySubs)).applyTo(res);
        res = this.tyMatchSubs.applyTo(res);
        return new Triple<HaskellSubstitution,HaskellSubstitution,HaskellExp>(tySubs,subs,(HaskellExp)res);
    }
}