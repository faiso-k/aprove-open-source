package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * An EntityMap consists of a map form name spaces to maps from names to entities.
 * It garantuees that Constructors and TypeConstructors are not mixed up
 * cause a name could occur in both namespaces.
 */
public class EntityMap extends HaskellObject.Visitable implements HaskellBean {
     public static enum NameSpace {NFTYPES,NFCONS,NFVARS,NFREST};
     Map<NameSpace,Map<String,HaskellEntity>> doubleMap;

     public EntityMap(){
         this.doubleMap = new HashMap<NameSpace,Map<String,HaskellEntity>>();
     }

     public void setDoubleMap(Map<NameSpace,Map<String,HaskellEntity>> doubleMap){
         this.doubleMap = doubleMap;
     }

     public Map<NameSpace,Map<String,HaskellEntity>> getDoubleMap(){
         return this.doubleMap;
     }

     /**
      * @returns the correct namespace for a given sort
      */
     private NameSpace getNF(HaskellEntity.Sort sort){
         if (HaskellEntity.Sort.TYPES.contains(sort)) {
            return NameSpace.NFTYPES;
        }
         if (HaskellEntity.Sort.CONSS.contains(sort)) {
            return NameSpace.NFCONS;
        }
         if (HaskellEntity.Sort.VARS.contains(sort)) {
            return NameSpace.NFVARS;
        }
         return NameSpace.NFREST;
     }

     public EntityMap(Set<HaskellEntity> core){
         this();
         for (HaskellEntity e : core){
             this.add(e);
         }
     }

     /**
      * addTo adds an entity to the dMap, used for intern convenience.
      */
     private void addTo(Map<NameSpace,Map<String,HaskellEntity>> dMap,HaskellEntity e){
         NameSpace nf = this.getNF(e.getSort());
         Map <String,HaskellEntity> lMap = dMap.get(nf);
         if (lMap == null) {
             lMap = new HashMap<String,HaskellEntity>();
             dMap.put(nf,lMap);
         }
         lMap.put(e.getName(),e);
     }

     public void add(HaskellEntity e){
         this.addTo(this.doubleMap,e);
     }

     public void remove(HaskellEntity e){
         Map <String,HaskellEntity> lMap = this.doubleMap.get(this.getNF(e.getSort()));
         if (lMap != null) {
            lMap.remove(e.getName());
         }
     }

     public void addAll(Set<HaskellEntity> es){
         for (HaskellEntity e : es) {
            this.add(e);
         }
     }

     public HaskellEntity get(String name,HaskellEntity.Sort sort){
         Map <String,HaskellEntity> lMap = this.doubleMap.get(this.getNF(sort));
         if (lMap == null) {
            return null;
        }
         HaskellEntity e = lMap.get(name);
         if (e == null) {
            return null;
        }
         if (e.getSort() != sort) {
            return null;
        }
         return e;
     }

     /**
      * @returns true, iff the name with given sort is already map to
      *                an entity by this entitymap
      */
     public boolean isDef(String name,HaskellEntity.Sort sort){
         Map <String,HaskellEntity> lMap = this.doubleMap.get(this.getNF(sort));
         if (lMap == null) {
            return false;
        }
         return lMap.get(name) != null;
     }

     public Set<HaskellEntity> values(){
         Set<HaskellEntity> res = new HashSet<HaskellEntity>();
         for (Map <String,HaskellEntity> lMap : this.doubleMap.values()){
             res.addAll(lMap.values());
         }
         return res;
     }

     @Override
    public HaskellObject deepcopy(){
         EntityMap nem = new EntityMap();
         for (Map <String,HaskellEntity> lMap : this.doubleMap.values()){
             for(HaskellEntity e : lMap.values()){
                 nem.add(e);
             }
         }
         return this.hoCopy(nem);
     }

     @Override
    public HaskellObject visit(HaskellVisitor hv){
         Map<NameSpace,Map<String,HaskellEntity>> dMap = new HashMap<NameSpace,Map<String,HaskellEntity>>();
         for (Map <String,HaskellEntity> lMap : this.doubleMap.values()){
             for(HaskellEntity e : lMap.values()){
                 this.addTo(dMap,this.walk(e,hv));
             }
         }
         this.doubleMap = dMap;
         return this;
     }

}
