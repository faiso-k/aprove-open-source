package aprove.verification.oldframework.Haskell.Collectors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 */
public class UsedEntityCollector extends HaskellVisitor{
    Set<HaskellEntity> usedEntities;
    Set<HaskellEntity> boundedEntities;

    /**
     */
    public UsedEntityCollector(Set<HaskellEntity> usedEntities){
        this.usedEntities = usedEntities;
    }

    @Override
    public boolean guardEntity(HaskellEntity ho){
        return this.usedEntities.add(ho);
    }

    @Override
    public boolean guardAssumptions(Modules ho){ return false;}
}
