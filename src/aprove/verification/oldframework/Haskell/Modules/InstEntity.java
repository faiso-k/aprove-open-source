package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The InstEntity represents an instance declaration as entity, it
 * contains the instance variable entities as the subentities.
 */

public class InstEntity extends HaskellEntity.TypeSkeleton implements EntityCollector,HaskellBean {
    Set<HaskellEntity> ivarEntities;

    /**
     * do not use this constructor, its only for bean convention
     */
    public InstEntity(){
    }

    /**
     * constructor for deepcopy
     */
    public InstEntity(String name,Module module,HaskellObject obj,Set<HaskellEntity> ivarEntities){
        super(name,HaskellEntity.Sort.INST,module,obj);
        this.setFixity(InfixDecl.FIXITY_DEFAULT);
        this.setPriority(InfixDecl.PRIORITY_DEFAULT);
        this.ivarEntities = ivarEntities;
    }

    /**
     * normal constructor
     */
    public InstEntity(String name,Module module,HaskellObject obj){
        this(name,module,obj,new HashSet<HaskellEntity>());
    }

    @Override
    public void setCollectedEntities(EntityMap em){
        this.ivarEntities = em.values();
        for (HaskellEntity e : this.getSubEntities()){
           e.setParentEntity(this);
        }
    }

    @Override
    public Set<HaskellEntity> getCollectedEntities(){
        return this.ivarEntities;
    }

    @Override
    public void addEntity(HaskellEntity e){
        e.setParentEntity(this);
        this.ivarEntities.add(e);
    }

    @Override
    public void removeEntity(HaskellEntity e){
        this.ivarEntities.remove(e);
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseEntity(this);
        if (hv.guardEntity(this)) {
            if (hv.guardValue(this)) {
                this.value = this.walk(this.value,hv);
            }
            if (hv.guardType(this)) {
                this.setType(this.walk(this.getType(),hv));
            }
            if (hv.guardMember(this)) {
                this.ivarEntities = this.listWalk(this.ivarEntities,hv);
            }
        }
        return hv.caseEntity(this);
    }

    @Override
    public Set<HaskellEntity> getSubEntities(){
        return this.ivarEntities;
    }

    public Set<HaskellEntity> getIvarEntities(){
        return this.ivarEntities;
    }

    public void setIvarEntities(Set<HaskellEntity> ivarEntities){
        this.ivarEntities = ivarEntities;
    }

    /**
     * @return the instance reduction rule of this instance
     */
    public ClassConstraintRule getConstraintRule(){
        return ((InstDecl)this.getValue()).getClassConstraintRule();
    }

    /**
     * sets the type of this entity to the instance type schema
     */
    public void instantiate(){
        this.setType(((InstDecl)this.getValue()).getInstTypeSchema());
    }

    /**
     * @returns the TyClassEntity for which this instance implements the member varibales
     */
    public HaskellEntity getTyClassEntity(){
        return ((InstDecl)this.getValue()).getTyClassEntity();
    }

    /**
     * @returns the TyConsEntity for which this instance implements the member varibales
     */
    public HaskellEntity getTyConsEntity(){
        return ((InstDecl)this.getValue()).getTyConsEntity();
    }

    /**
     * @returns the instance type of this instance
     */
    public HaskellType getInstTypeTerm(){
        return ((InstDecl)this.getValue()).getInstTypeTerm();
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new InstEntity(this.name,this.module,Copy.deep(this.getValue()),new HashSet<HaskellEntity>(this.ivarEntities)));
    }

}
