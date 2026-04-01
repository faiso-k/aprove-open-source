package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * An EntityFrame represent a scope of seen variables in expression
 * some expressions carries a entiyframe (LambdaExp,LetExp ...).
 * it is cascaded with the next higer frame up to the module
 * XML-Bean
 */

public interface EntityFrame extends EntityCollector {

     /**
      * Get Entity for a local refrence (uses parentEntityFrame frame)
      */
     public HaskellEntity getLocalEntity(HaskellSym sym,HaskellEntity.Sort sort);

     /**
      * Get an Entity out of this frame but not out of parentEntityFrame frames
      */
     public HaskellEntity getFrameEntity(HaskellSym sym,HaskellEntity.Sort sort);


     public void setParentEntityFrame(EntityFrame entityFrame);

     public EntityFrame getParentEntityFrame();

     public class EntityFrameSkeleton extends HaskellObject.HaskellObjectSkeleton implements EntityFrame, HaskellBean {
        public EntityFrame parentEntityFrame;
        public EntityMap entityMap;

        /**
         * do not use this constructor, its only for bean convention
         */
        public EntityFrameSkeleton(){
        }

        public EntityFrameSkeleton(EntityFrame parentEntityFrame){
            this.parentEntityFrame = parentEntityFrame;
            this.entityMap = null;
        }

        public EntityFrameSkeleton(EntityFrame parentEntityFrame,EntityMap entityMap){
            this.parentEntityFrame = parentEntityFrame;
            this.entityMap = entityMap;
        }

        @Override
        public void setParentEntityFrame(EntityFrame entityFrame){
            this.parentEntityFrame = entityFrame;
        }

        @Override
        public EntityFrame getParentEntityFrame(){
            return this.parentEntityFrame;
        }

        public void setEntityMap(EntityMap entityMap){
            this.entityMap = entityMap;
        }

        public EntityMap getEntityMap(){
            return this.entityMap;
        }

        @Override
        public void setCollectedEntities(EntityMap entities){
            this.entityMap = entities;
        }

        @Override
        public Set<HaskellEntity> getCollectedEntities(){
            return this.entityMap.values();
        }

        @Override
        public HaskellEntity getLocalEntity(HaskellSym sym,HaskellEntity.Sort sort){
            HaskellEntity e = this.getFrameEntity(sym,sort);
            if (e != null) {
           return e;
        }
            return this.parentEntityFrame.getLocalEntity(sym,sort);
        }

        @Override
        public HaskellEntity getFrameEntity(HaskellSym sym,HaskellEntity.Sort sort){
            if ("".equals(sym.getQualifier())) {
               return this.entityMap.get(sym.getName(false),sort);
            }
            return null;
        }

        @Override
        public HaskellObject visit(HaskellVisitor hv){
            if (hv.guardEntityFrame(this)){
                hv.fcaseEntityFrame(this);
                this.entityMap = this.walk(this.entityMap,hv);
                hv.icaseEntityFrame(this);
            }
            return hv.caseEntityFrame(this);
        }

        @Override
        public void addEntity(HaskellEntity e){
            this.entityMap.add(e);
        }

        @Override
        public void removeEntity(HaskellEntity e){
            this.entityMap.remove(e);
        }

        @Override
        public HaskellObject deepcopy(){
            return this.hoCopy(new EntityFrame.EntityFrameSkeleton(this.parentEntityFrame,Copy.deep(this.entityMap)));
        }

        @Override
        public String toString(){
            return ""+this.entityMap.values();
        }
    }
}
