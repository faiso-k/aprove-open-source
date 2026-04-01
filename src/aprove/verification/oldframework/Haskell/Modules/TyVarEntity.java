package aprove.verification.oldframework.Haskell.Modules;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * TyVarEntity represents a type variable
 *
 */

public class TyVarEntity extends VarEntity{

    /**
     * do not use this constructor, its only for bean convention
     */
    public TyVarEntity(){
    }

    /**
     * normal constructor
     */
    public TyVarEntity(String name,Module module,HaskellObject obj,HaskellObject type){
        super(name,module,obj,type);
        this.sort = HaskellEntity.Sort.TYVAR;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new TyVarEntity(this.name,this.module,
           Copy.deep(this.getValue()),Copy.deep(this.getType())));
    }

}
