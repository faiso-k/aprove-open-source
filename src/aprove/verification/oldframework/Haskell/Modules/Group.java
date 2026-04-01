package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * A group is a set of HaskellEntities with automatic module range detection.
 *
 * order is needed in TypeInferenceVisitor so it is a LinkedHashSet!!
 */
public class Group extends LinkedHashSet<HaskellEntity> implements HaskellBean {
    Set<Module> modules;

    public Group(){
         super();
         this.modules = new HashSet<Module>();
    }

    public Group(HaskellEntity e){
         this();
         this.add(e);
    }

    public Group(Collection<HaskellEntity> es){
         this();
         this.addAll(es);
    }

    @Override
    public boolean add(HaskellEntity e){
         this.modules.add(e.getModule());
         return super.add(e);
    }

    public void setModules(Set<Module> modules){
         this.modules = modules;
    }

    public Set<Module> getModules(Set<Module> modules){
         return this.modules;
    }

    /**
     * @return true, iff the entities are declared in more the one module
     */
    public boolean isMultiGroup(){
         return this.modules.size() > 1;
    }

    /**
     * @return true, iff the entities in this group are all declared in the prelude
     */
    public boolean isPreludeGroup(){
         if (this.modules.size() == 1) {
            Module m = this.modules.iterator().next();
            if (m.isPrelude()){
               return !m.isAccessible();
            }
         }
         return false;
    }


    /**
     * @return true iff the entities of this group are all declared in modules that were already loaded
     */
    public boolean isAlreadyLoadedGroup() {
        if (this.modules.size() == 1) {
            Module m = this.modules.iterator().next();
            return m.isAlreadyLoaded();
        }
        return false;
    }

    public Module getGroupModule(){
         if (this.modules.size() == 1) {
             return this.modules.iterator().next();
         }
         return null;
    }


}
