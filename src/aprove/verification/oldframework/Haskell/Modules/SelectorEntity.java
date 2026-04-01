package aprove.verification.oldframework.Haskell.Modules;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Matthias Raffelsieper
 * @version $Id$
 */

public class SelectorEntity extends HaskellEntity.TypeSkeleton{

    /**
     * do not use this constructor, its only for bean convention
     */
    public SelectorEntity(){
    }

    /**
     * VarEntity for selectors
     */
    public SelectorEntity(String name,Module module,HaskellObject obj,HaskellObject type){
        super(name,HaskellEntity.Sort.VAR,module,obj);
        this.type = type;
    }


    @Override
    public Object deepcopy(){
        return this.hoCopy(new SelectorEntity(this.name,this.module,Copy.deep(this.getValue()),Copy.deep(this.getType())));
    }

}
