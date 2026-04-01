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

public class ArgumentCombinator implements Collection_Util.Combinator<Triple<HaskellSubstitution,HaskellSubstitution,HaskellExp>>{
     Atom atom;
     NarrowingGraphAnalyser nga;
     HaskellSubstitution ptySubs;
     HaskellSubstitution psubs;

     public ArgumentCombinator(Atom atom,HaskellSubstitution ptySubs,HaskellSubstitution psubs,NarrowingGraphAnalyser nga){
         this.atom = atom;
         this.nga = nga;
         this.ptySubs = ptySubs;
         this.psubs = psubs;
     }

     @Override
    public Triple<HaskellSubstitution,HaskellSubstitution,HaskellExp> combine(Object[] objs){
         HaskellSubstitution tySubs = this.ptySubs;
         HaskellSubstitution subs = this.psubs;
         List<HaskellExp> exps = new Vector<HaskellExp>();
         exps.add(this.atom);
         for (Object obj : objs){
            Triple triple = (Triple) obj;
            tySubs = tySubs.combineWith((HaskellSubstitution) triple.x);
            subs = subs.combineWith((HaskellSubstitution) triple.y);
            HaskellExp arg = (HaskellExp) triple.z;
            exps.add(arg);
         }
         for (int i=0; i < exps.size(); i++){
            exps.set(i,(HaskellExp) subs.applyTo((BasicTerm)exps.get(i)));
         }
         for (int i=0; i < exps.size(); i++){
            (new TypeAnnotationSubstitutor(tySubs)).applyTo(exps.get(i));
         }
         HaskellExp head = exps.remove(0);
         HaskellExp exp = (HaskellExp) this.nga.prelude.buildApplies(head,exps);
         return new Triple<HaskellSubstitution,HaskellSubstitution,HaskellExp>(tySubs,subs,exp);
     }
}