package aprove.verification.oldframework.Haskell.Modules;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 */

public class VarEntity extends HaskellEntity.TypeSkeleton{
    public boolean local;
    public boolean hidden;

    /**
     * do not use this constructor, its only for bean convention
     */
    public VarEntity(){
    }

    /**
     * VarEntity for functions
     */
    public VarEntity(String name,Module module,HaskellObject obj,HaskellObject type){
        super(name,HaskellEntity.Sort.VAR,module,obj);
        this.type = type;
        this.local = false;
        this.hidden = false;
    }

    /**
     * @param local true the variable is only in patterns
     *              false the variable represents function
     */
    public VarEntity(String name,Module module,HaskellObject obj,HaskellObject type,boolean local){
        super(name,HaskellEntity.Sort.VAR,module,obj);
        this.type = type;
        this.local = local;
        this.hidden = false;
    }

    /**
     * constructor for deepcopy
     * @param local true the variable is only in patterns
     *              false the variable represents function
     */
    public VarEntity(String name,Module module,HaskellObject obj,HaskellObject type,boolean local,boolean hidden){
        super(name,HaskellEntity.Sort.VAR,module,obj);
        this.type = type;
        this.local = local;
        this.hidden = hidden;
    }

    public boolean isHidden(){
        return this.hidden;
    }

    public boolean getHidden(){
        return this.hidden;
    }

    public void setHidden(boolean hidden){
        this.hidden = hidden;
    }

    public void setLocal(boolean local){
        this.local = local;
    }

    public boolean getLocal(){
        return this.local;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new VarEntity(this.name,this.module,Copy.deep(this.getValue()),Copy.deep(this.getType()),this.local,this.hidden));
    }

}
