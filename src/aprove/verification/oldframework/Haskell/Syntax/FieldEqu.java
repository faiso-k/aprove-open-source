package aprove.verification.oldframework.Haskell.Syntax;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 * FieldEqu represents a Field setting like var = exp
 * in a Record constructor of Haskell
 * but this is ignored currently
 */
public class FieldEqu extends HaskellObject.HaskellObjectSkeleton {
     Var var;
     HaskellExp exp;

     public FieldEqu(Var var,HaskellExp exp){
         this.var = var;
         this.exp = exp;
     }

     public HaskellPat getVariable(){
         return this.var;
     }

     public HaskellExp getExpression(){
         return this.exp;
     }

     @Override
    public Object deepcopy(){
        return this.hoCopy(new FieldEqu(Copy.deep(this.var),Copy.deep(this.exp)));
     }

     @Override
    public HaskellObject visit(HaskellVisitor hv){
         //this.var = walk(var,hv);
         this.exp = this.walk(this.exp,hv);
         return this;
     }


     @Override
    public String toString() {
         return "Field "+this.var+" = "+this.exp;
     }
}
