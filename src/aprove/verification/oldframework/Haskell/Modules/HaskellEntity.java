package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The HaskellEntity is the central interface of the Haskell representation,
 * it provids access to name, module, sort, sub entities, parent, value and type of an
 * entitiy. An entity is a common representation of Modules, Data-Constructors, Type-Constructors,
 * function-variables, local-variables, type-variables, instances,classes
 * thier representing objects all implements the HaskellEntity
 */
public interface HaskellEntity extends HaskellObject,HaskellExp {

     /**
      * the Sort for distinguishing the entities
      */
     public static enum Sort {
         MODULE,TYCLASS,TYCONS,TYVAR,INST,CONS,VAR,IVAR,FVAR,PATDECL;
         public final static Set<Sort> TYPES = EnumSet.of(Sort.TYCLASS,Sort.TYCONS,Sort.TYVAR);
         public final static Set<Sort> CONSS = EnumSet.of(Sort.CONS);
         public final static Set<Sort> VARS  = EnumSet.of(Sort.VAR);
         public final static Set<Sort> TYCS  = EnumSet.of(Sort.TYCLASS,Sort.TYCONS);
         public final static Set<Sort> UPCASE = EnumSet.of(Sort.TYCLASS,Sort.TYCONS,Sort.CONS,Sort.MODULE);
     };

     /**
      * @returns the name of the entity
      */
     public String getName();

     /**
      * @returns the module where this entity is defined
      */
     public Module getModule();
     public void setModule(Module module);

     /**
      * @returns the sort of this entity
      */
     public HaskellEntity.Sort getSort();

     /**
      * @returns the subentities of an entity (Type-Constructors have constructors, Classes have members)
      * changing the returned set means changing the entity
      */
     public Set<HaskellEntity> getSubEntities();

     /**
      * @returns the parent entity (constructors have Type-Constructors as parents)
      */
     public HaskellEntity getParentEntity();
     public void setParentEntity(HaskellEntity e);

     /**
      * @returns the fixity of this entity (variables or (Type-)constructors may have special fixity)
      */
     public int getFixity();
     public void setFixity(int fixity);

     /**
      * @returns the priority of this entity (variables or (Type-)constructors may have special priority)
      */
     public int getPriority();
     public void setPriority(int priority);

     /**
      * @returns the value of this entity (i.e. the real represented object, so functions)
      */
     public HaskellObject getValue();
     public void setValue(HaskellObject value);

     /**
      * @returns the type of this entity (i.e. the typeschema of the variables, constructors, type-constructors)
      */
     public HaskellObject getType();
     public void setType(HaskellObject type);

     /**
      * @returns the with of the tuple if this entity represents a tuple
      */
     public int getTuple();

     /**
      * destroies the entity by removing it from the module context and removing it form
      * subentitie-set of the parent entity
      */
     public void destroy();

     /**
      * basic skeleton for several entities
      * it offers name, sort, module, value, priority and fixity which is comon for several entities,
      * a visit for the value and the type, and the hoCopy method offers convenience for deepcopy
      */
     public abstract class HaskellEntitySkeleton extends HaskellObject.HaskellObjectSkeleton implements HaskellBean, HaskellEntity {
         //private static int count = 0;
         public static int count = 0;
         public transient int num;

         String name;
         HaskellEntity.Sort sort;
         Module module;
         HaskellObject value;
         int priority;
         int fixity;

         public HaskellEntitySkeleton(){
         }

         public HaskellEntitySkeleton(String name,HaskellEntity.Sort sort,Module module,HaskellObject value){
             this.num = HaskellEntitySkeleton.count;
             HaskellEntitySkeleton.count++;
             this.name = name;
             this.sort = sort;
             this.module = module;
             this.value = value;
             this.priority = InfixDecl.PRIORITY_DEFAULT;
             this.fixity = InfixDecl.FIXITY_DEFAULT;
         }

         @Override
        public String getName(){
             return this.name;
         }

         public void setName(String name){
             this.name = name;
         }

         @Override
        public Module getModule(){
             return this.module;
         }

         @Override
        public void setModule(Module module){
             this.module = module;
         }

         @Override
        public void destroy(){
             this.module.removeEntity(this);
         }

         @Override
        public HaskellEntity.Sort getSort(){
             return this.sort;
         }

         public void setSort(HaskellEntity.Sort sort){
             this.sort = sort;
         }

         @Override
        public Set<HaskellEntity> getSubEntities(){
             return null;
         }

         @Override
        public HaskellEntity getParentEntity(){
             return null;
         }

         @Override
        public void setParentEntity(HaskellEntity e){
         }

         @Override
        public void setValue(HaskellObject value){
             this.value = value;
         }

         @Override
        public HaskellObject getValue(){
             return this.value;
         }

         @Override
        public HaskellObject getType(){
             return null;
         }

         @Override
        public void setType(HaskellObject type){
         }

         @Override
        public int getTuple(){
             return -1;
         }

         @Override
        public void setFixity(int fixity){
             this.fixity = fixity;
         }

         @Override
        public int getFixity(){
             return this.fixity;
         }

         @Override
        public void setPriority(int priority){
             this.priority = priority;
         }

         @Override
        public int getPriority(){
             return this.priority;
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
             }
             return hv.caseEntity(this);
         }

         @Override
        public String toString(){
             return this.sort+"_"+this.name;
         }

         @Override
        public HaskellObject hoCopy(HaskellObject s){
             HaskellEntity.HaskellEntitySkeleton e = (HaskellEntity.HaskellEntitySkeleton) s;
             e.setFixity(this.getFixity());
             e.setPriority(this.getPriority());
             e.setParentEntity(this.getParentEntity());
             return super.hoCopy(e);
         }

     }

     /**
      * offers the same as the basic skeleton
      * and additional the type
      */
     public abstract class TypeSkeleton extends HaskellEntity.HaskellEntitySkeleton implements HaskellBean {
         protected HaskellObject type;

         public TypeSkeleton(){
             super();
         }

         public TypeSkeleton(String name,HaskellEntity.Sort sort,Module module,HaskellObject value){
             super(name,sort,module,value);
             this.type = null;
         }

         @Override
        public HaskellObject getType(){
             return this.type;
         }

         @Override
        public void setType(HaskellObject type){
             this.type = type;
         }

         @Override
        public HaskellObject hoCopy(HaskellObject ts){
             ((HaskellEntity.TypeSkeleton)ts).type = Copy.deep(this.type);
             return super.hoCopy(ts);
         }

     }

}
