package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Substitutors.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * EntityAssumptions carries the type asspumtions
 * by directly changing the type of a given entity (pushAssumption).
 * It takes care for which entities types were asked and
 * it assums all types are null at start of using it.
 *
 */
public class EntityAssumptions extends HaskellObject.Visitable implements Assumptions {
    Set<HaskellEntity> entities;

    public EntityAssumptions(){
        this.entities = new HashSet<HaskellEntity>();
    }

    public EntityAssumptions(Collection<HaskellEntity> entities){
        this.entities = new HashSet<HaskellEntity>(entities);
    }

    public void setEntities(Set<HaskellEntity> entities){
        this.entities = entities;
    }

    public Set<HaskellEntity> getEntities(){
        return this.entities;
    }

    @Override
    public void keepOnly(Collection<HaskellEntity> rEntities){
        this.entities.retainAll(rEntities);
    }

    @Override
    public void pushAssumption(HaskellEntity e,TypeSchema ts){
        this.entities.add(e);
        e.setType(ts);
    }

    public List<Pair<HaskellEntity,TypeSchema>> getAssumptions(){
        return null;
    }

    public void pushAssumption(HaskellEntity e){
        this.entities.add(e);
    }

    @Override
    public TypeSchema getTypeSchemaFor(HaskellEntity e){
        this.entities.add(e);
        return (TypeSchema) e.getType();
    }

    @Override
    public Object deepcopy(){
        return new EntityAssumptions(this.entities);
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        if (hv.guardAssumptionEntities(this)){
            this.entities = this.listWalk(this.entities,hv);
        }
        for (HaskellEntity e : this.entities){
            e.setType(this.walk(e.getType(),hv));
        }
        return this;
    }

    @Override
    public void refine(HaskellSubstitution subs){
        this.visit(new VarSubstitutor(subs));
    }

    @Override
    public String toString(){
        String r = "";
        for (HaskellEntity e : this.entities){
            r = r +"\n"+e.getName()
                  +"   ----   "+e.getType();
        }
        return r;
    }

}
