package aprove.verification.oldframework.Haskell.Transformations;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Substitutors.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 */

public class ReductionFrame{
    Map<HaskellEntity,HaskellObject> eMap = new HashMap<HaskellEntity,HaskellObject>();
    Set<HaskellEntity> forRemove = new HashSet<HaskellEntity>();
    Set<HaskellEntity> forAdd = new HashSet<HaskellEntity>();

    public void addEntity(HaskellEntity e){
        this.forAdd.add(e);
    }

    public void removeEntity(HaskellEntity e){
        this.forRemove.add(e);
    }

    public void putVarRep(HaskellEntity e,HaskellObject ho){
        Map<HaskellEntity,HaskellObject> cMap = new HashMap<HaskellEntity,HaskellObject>();
        cMap.put(e,ho);
        VarEntitySubstitutor ves = new VarEntitySubstitutor(cMap);
        Map<HaskellEntity,HaskellObject> rMap = new HashMap<HaskellEntity,HaskellObject>();
        for (Map.Entry<HaskellEntity,HaskellObject> me : this.eMap.entrySet()){
            rMap.put(me.getKey(),me.getValue().visit(ves));
        }
        rMap.put(e,ho);
        this.eMap = rMap;
    }

    public void updateEntityFrame(EntityFrame ef){
        for (HaskellEntity e : this.forRemove){
            ef.removeEntity(e);
        }
        for (HaskellEntity e : this.forAdd){
            ef.addEntity(e);
        }
    }

    public HaskellObject replace(HaskellObject ho){
        return ho.visit(new VarEntitySubstitutor(this.eMap));
    }

    public HaskellObject replaceAndUpdate(EntityFrameCarrier ho){
        this.updateEntityFrame(ho.getEntityFrame());
        return this.replace(ho);
    }
}
