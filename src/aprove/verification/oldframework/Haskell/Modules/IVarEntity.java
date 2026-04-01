package aprove.verification.oldframework.Haskell.Modules;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The IVarEntity represent a instance of a class variable, the parentEntity entity is the
 * proper InstEntity
 */

public class IVarEntity extends VarEntity implements HaskellBean{
    HaskellEntity parentEntity;

    /**
     * do not use this constructor, its only for bean convention
     */
    public IVarEntity(){
    }

    /**
     * normal constructor
     */
    public IVarEntity(String name,Module module,HaskellObject obj,HaskellObject type){
        super(name,module,obj,type);
        this.sort = HaskellEntity.Sort.IVAR;
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
        ((InstEntity)this.getParentEntity()).removeEntity(this);
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new IVarEntity(this.name,this.module,Copy.deep(this.getValue()),Copy.deep(this.getType())));
    }

    /**
     * sets the concrete type(-schema) of this entity by asking the parentEntity which
     * type constructor is used in the class constraint.
     */
    public void instantiate(){
        //InstDecl id = (InstDecl) this.getParentEntity().getValue();
        //HaskellEntity tce = id.getTyClassEntity();
        HaskellEntity tce = ((InstEntity) this.getParentEntity()).getTyClassEntity();
        TypeSchema instance = (TypeSchema) this.getParentEntity().getType();
        HaskellEntity cvarEntity = ((InstFunction) this.getValue()).getMemberForInst();
        if (cvarEntity.getParentEntity() != tce){
            HaskellError.output(this.getValue(),this.getName()+" is not member of class "+tce.getName());
        }
        MemberTypeSchema mts = (MemberTypeSchema) cvarEntity.getType();
        this.setType(mts.instantiate(instance));
    }

}
