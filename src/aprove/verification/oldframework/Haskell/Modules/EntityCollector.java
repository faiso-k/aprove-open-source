package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * Some HaskellObject (Module, EntityFrame, TyConsEntity, InstEntity)
 * carries HaskellEntities and implement this interface for abstraction
 */

public interface EntityCollector extends HaskellObject {

     public void setCollectedEntities(EntityMap em);
     public Set<HaskellEntity> getCollectedEntities();
     public void addEntity(HaskellEntity e);
     public void removeEntity(HaskellEntity e);

}
