package aprove.verification.oldframework.Haskell.Modules;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * CVarEntity represents a member variables of class
 *
 */

public class CVarEntity extends VarEntity implements HaskellBean {
    HaskellEntity parentEntity;

    /**
     * do not use this constructor, its only for bean convention
     */
    public CVarEntity(){
        super();
    }

    /**
     * constructor for deepcopy
     */
    public CVarEntity(String name,Module module,HaskellObject obj,HaskellObject type){
        super(name,module,obj,type);
        this.sort = HaskellEntity.Sort.VAR;
    }

    @Override
    public void setParentEntity(HaskellEntity parentEntity){
        this.parentEntity = parentEntity;
    }

    @Override
    public HaskellEntity getParentEntity(){
        return this.parentEntity;
    }

    @Override
    public void destroy(){
        super.destroy();
        ((TyClassEntity)this.getParentEntity()).removeEntity(this);
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new CVarEntity(this.name,this.module,Copy.deep(this.getValue()),Copy.deep(this.getType())));
    }

}
