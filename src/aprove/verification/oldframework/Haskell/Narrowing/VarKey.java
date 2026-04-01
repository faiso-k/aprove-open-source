/**
 *
 */
package aprove.verification.oldframework.Haskell.Narrowing;

import aprove.verification.oldframework.Haskell.BasicTerms.*;

public class VarKey {
    Var var;
    public VarKey(Var var){
        this.var = var;
    }

    @Override
    public boolean equals(Object obj){
        if (obj instanceof VarKey){
            VarKey vk = (VarKey) obj;
            return (vk.var.getSymbol().getEntity() == this.var.getSymbol().getEntity())
                   && (vk.var.getTypeTerm().equivalentTo(this.var.getTypeTerm()));
        }
        return false;
    }

    @Override
    public int hashCode(){
        return this.var.getSymbol().getEntity().hashCode();
    }
}