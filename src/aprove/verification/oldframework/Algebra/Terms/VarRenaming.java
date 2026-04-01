package aprove.verification.oldframework.Algebra.Terms;

import java.util.*;

import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/**
 * This is a special kind of substitution, where all values are variables, too.
 * Thus an inverse-operation exists
 * @author Eugen Yu
 * @version $Id$
 */

public class VarRenaming extends AlgebraSubstitution{

    protected VarRenaming(HashMap<VariableSymbol,AlgebraTerm> map){
      super(map);
    }

    public static AlgebraSubstitution create(){
      return new VarRenaming(new HashMap<VariableSymbol,AlgebraTerm>() );
    }

    public static VarRenaming createVarRen(){
        return new VarRenaming(new HashMap<VariableSymbol,AlgebraTerm>() );
    }

    //Accessors

    public AlgebraVariable getVar(VariableSymbol vsym){
      return (AlgebraVariable)super.get(vsym);
    }

    public void putVar(VariableSymbol vsym, AlgebraVariable var){
      super.put(vsym, var);
    }


    /**
     * Since all elements are variables as well, we can
     * @return a substitution that is inverse to this substitution
     */
    public VarRenaming getInverse(){
      VarRenaming result = (VarRenaming)VarRenaming.create();

      for (Iterator  i = this.getDomain().iterator();
           i.hasNext();){
           VariableSymbol vsym = (VariableSymbol)i.next();
           AlgebraVariable varKey = AlgebraVariable.create(vsym);

           AlgebraVariable  varElement = (AlgebraVariable)this.map.get(vsym);

           result.putVar(varElement.getVariableSymbol(), varKey);
      }
      return result;
    }


    //getIdentitaty
    public static VarRenaming getIdentity(Set<AlgebraVariable> sv){
        VarRenaming result = (VarRenaming) VarRenaming.create();
        for (Iterator i = sv.iterator(); i.hasNext();){
        AlgebraVariable var = (AlgebraVariable)i.next();
        result.putVar(var.getVariableSymbol(), var);
        }
        return result;
    }

    /** Creates a substitution that renames the variables in V into new variables that are not in W.
    */
     public static VarRenaming createRenaming(Set<AlgebraVariable> V, Set<AlgebraVariable> W) {
         Iterator i = V.iterator();

         /* rename away from W*/
         FreshVarGenerator vargen = new FreshVarGenerator(W);
         VarRenaming ren = VarRenaming.createVarRen();

         while(i.hasNext()) {
             AlgebraVariable v = (AlgebraVariable)i.next();
             AlgebraVariable w = vargen.getFreshVariable(v, true);
             ren.put(v.getVariableSymbol(), w);
         }

         return ren;
     }
}

