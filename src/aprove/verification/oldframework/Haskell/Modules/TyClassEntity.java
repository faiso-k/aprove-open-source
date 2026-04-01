package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * TyClassEntity represents a class declared by an class-declaration
 * it contains the member variables (CVarEntity) as SubEntities
 *
 */

public class TyClassEntity extends HaskellEntity.TypeSkeleton implements EntityCollector {
    //public static int cNum = 0;
    Set<HaskellEntity> cvarEntities;

    /**
     * do not use this constructor, its only for bean convention
     */
    public TyClassEntity(){
    }

    /**
     * constructor for deepcopy
     */
    public TyClassEntity(String name,Module module,HaskellObject obj,Set<HaskellEntity> cvarEntities){
        super(name,HaskellEntity.Sort.TYCLASS,module,obj);
        this.setFixity(InfixDecl.FIXITY_DEFAULT);
        this.setPriority(InfixDecl.PRIORITY_DEFAULT);
        this.cvarEntities = cvarEntities;
    }

    /**
     * normal constructor
     */
    public TyClassEntity(String name,Module module,HaskellObject obj){
        this(name,module,obj,new HashSet<HaskellEntity>());
    }

    @Override
    public Set<HaskellEntity> getSubEntities(){
        return this.cvarEntities;
    }

    public void setCvarEntities(Set<HaskellEntity> cvarEntities){
        this.cvarEntities = cvarEntities;
    }

    public Set<HaskellEntity> getCvarEntities(){
        return this.cvarEntities;
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
                this.cvarEntities = this.listWalk(this.cvarEntities,hv);
            }
        }
        return hv.caseEntity(this);
    }

    /**
     * @returns the ClassConstraintRule representing the head of the class represented
     * by this TyClassEntity
     */
    public ClassConstraintRule getConstraintRule(){
        return ((ClassDecl)this.getValue()).getClassConstraintRule();
    }

    @Override
    public void setCollectedEntities(EntityMap em){
        this.cvarEntities = em.values();
        this.module.addLinkEntities(this.cvarEntities);
        ClassDecl cd = (ClassDecl) this.getValue();
        for (HaskellEntity e : this.getSubEntities()){
           e.setParentEntity(this);
           if (e.getType() == null) {
               HaskellError.output(e.getValue(),"missing type signature for function");
           } else {
               HaskellPreType type = (HaskellPreType) e.getType();
               type.setClassConstraint(cd.getNewConstraint(type));
           }
        }
    }

    @Override
    public Set<HaskellEntity> getCollectedEntities(){
        return this.cvarEntities;
    }

    @Override
    public void addEntity(HaskellEntity e){
        this.cvarEntities.add(e);
    }

    @Override
    public void removeEntity(HaskellEntity e){
        this.cvarEntities.remove(e);
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new TyClassEntity(this.name,this.module,Copy.deep(this.getValue()),
        new HashSet<HaskellEntity>(this.cvarEntities)));
    }

}
