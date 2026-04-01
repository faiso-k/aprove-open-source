package aprove.verification.oldframework.Haskell.Modules;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * TySynEntity represents a type declaration
 * but the type synonyms are replaced in all types
 *
 */

public class TySynEntity extends HaskellEntity.TypeSkeleton{

    /**
     * do not use this constructor, its only for bean convention
     */
    public TySynEntity(){
    }

    /**
     * normal constructor
     */
    public TySynEntity(String name,Module module,HaskellObject obj){
        super(name,HaskellEntity.Sort.TYCONS,module,obj);
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new TySynEntity(this.name,this.module,Copy.deep(this.getValue())));
    }

}
