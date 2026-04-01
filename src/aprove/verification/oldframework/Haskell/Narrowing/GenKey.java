package aprove.verification.oldframework.Haskell.Narrowing;

import aprove.verification.oldframework.Haskell.Modules.*;


public class GenKey{
    HaskellEntity entity;
    int arity;

    public GenKey(HaskellEntity entity,int arity){
        this.entity = entity;
        this.arity = arity;
    }

    @Override
    public boolean equals(Object obj){
        if (!(obj instanceof GenKey)) {
            return false;
        }
        GenKey gk = (GenKey)obj;
        if (gk.arity != this.arity) {
            return false;
        }
        if (gk.entity != this.entity) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode(){
        return this.arity+4*this.entity.hashCode();
    }

    @Override
    public String toString(){
        return this.entity+"/"+this.arity;
    }

}
