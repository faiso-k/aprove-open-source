package aprove.verification.oldframework.Typing;
import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Basic class for representing type quantifier of type schemes.
 * @author Stephan Swiderski
 * @version $Id$
 */

public class TypeQuantifier extends LinkedHashSet<AlgebraTerm> {

   /**
    * creates a new empty type quantifier.
    */
   public TypeQuantifier(){
       super();
   }

   /**
    * creates a new type quantifier with a given set of Variables
    * @param allQuans the set of Variables
    */
   public TypeQuantifier(Set<AlgebraVariable> allQuans){
       super(allQuans);
   }

   /**
    * build a Substitution for renaming the quantifed variables
    * in fresh ones.
    * @param fvg fresh var generator cause of renamings
    * @return substitution for some type terms in context of this quantifier
    */
   public AlgebraSubstitution freshVarRename(FreshVarGenerator fvg){
       AlgebraSubstitution subs = AlgebraSubstitution.create();
       Iterator it = this.iterator();
       while (it.hasNext()){
          AlgebraVariable curVar = (AlgebraVariable)it.next();
          AlgebraVariable freshVar = TypeTools.getFreshTypeVariable(fvg);
      subs.put(curVar.getVariableSymbol(),(AlgebraTerm)freshVar);
       }
       return subs;
   }

   /**
    * renames all quantified variables in fresh ones.
    * @param fvg fresh var generator cause of renamings
    * @return substitution for some type terms in context of this quantifier
    */
   public AlgebraSubstitution refreshVars(FreshVarGenerator fvg){
       Set<AlgebraVariable> nAllQuans = new HashSet<AlgebraVariable>();
       AlgebraSubstitution subs = AlgebraSubstitution.create();
       Iterator it = this.iterator();
       while (it.hasNext()){
          AlgebraVariable curVar = (AlgebraVariable)it.next();
          AlgebraVariable freshVar = TypeTools.getFreshTypeVariable(fvg);
      subs.put(curVar.getVariableSymbol(),(AlgebraTerm)freshVar);
      nAllQuans.add(freshVar);
       }
       this.clear();
       this.addAll(nAllQuans);
       return subs;
   }

   /**
    * A deep copy of this quantifier (in same type context).
    * The contained variables are copyied too.
    * The symbols of these variables are retained unchanged.
    */
   public TypeQuantifier deepcopy(){
       Set<AlgebraVariable> nAllQuans = new HashSet<AlgebraVariable>();
       Iterator it = this.iterator();
       while (it.hasNext()){
           AlgebraVariable curVar = (AlgebraVariable)it.next();
           nAllQuans.add((AlgebraVariable) curVar.deepcopy());
       }
       return new TypeQuantifier(nAllQuans);
    }

   /**
    * Build a string representation of this quantifier.
    * @return the string which represents this quantifier
    */
   @Override
public String toString(){
       String qus= new String("<");
       Iterator it = this.iterator();
       String tr = "";
       while (it.hasNext()){
          AlgebraVariable curVar = (AlgebraVariable)it.next();
      qus = tr + qus + curVar.getName();
      tr = ".";
       }
       return qus+">";
   }

}
