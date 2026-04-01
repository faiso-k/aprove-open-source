package aprove.verification.oldframework.Haskell.Collectors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 * FreeEntityCollector collects free entities (not bounded by an EntityFrame)
 * and it could also collect the bounded entities on the fly
 */
public class FreeEntityCollector extends HaskellVisitor{
    Set<HaskellEntity> freeEntities;
    Set<HaskellEntity> boundedEntities;

    /**
     *  @param freeEntities target set for free entities
     */
    public FreeEntityCollector(Set<HaskellEntity> freeEntities){
        this.freeEntities = freeEntities;
        this.boundedEntities = null;
    }

    /**
     *  @param freeEntities target set for free entities
     *  @param boundedEntities target set for bounded entities
     */
    public FreeEntityCollector(Set<HaskellEntity> freeEntities,Set<HaskellEntity> boundedEntities){
        this.freeEntities = freeEntities;
        this.boundedEntities = boundedEntities;
    }

    @Override
    public void fcaseHaskellNamedSym(HaskellNamedSym ho){
        this.freeEntities.add(ho.getEntity());
    }

    @Override
    public void icaseEntityFrame(EntityFrame ho){
        this.freeEntities.removeAll(ho.getCollectedEntities());
        if (this.boundedEntities != null){
            this.boundedEntities.addAll(ho.getCollectedEntities());
        }
    }

}
