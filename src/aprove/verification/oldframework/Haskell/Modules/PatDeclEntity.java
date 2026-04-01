package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 * The PatDeclEntity carries a Pattern Declaration.
 *
 */

public class PatDeclEntity extends HaskellEntity.TypeSkeleton{
    private static int counter = 0;
    public Set<HaskellEntity> subEntities;

    public PatDeclEntity(){
    }

    public PatDeclEntity(Module module,HaskellObject obj,HaskellObject type,Set<HaskellEntity> subEntities){
        super(""+PatDeclEntity.counter,HaskellEntity.Sort.PATDECL,module,obj);
        PatDeclEntity.counter++;
        this.type = type;
        this.subEntities = subEntities;
    }

    public void setSubEntities(Set<HaskellEntity> subEntities){
        this.subEntities = subEntities;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new PatDeclEntity(this.module,Copy.deep(this.getValue()),Copy.deep(this.getType()),
               new HashSet<HaskellEntity>(this.subEntities)));
    }

    public PatDeclEntity(Module module,HaskellObject obj,HaskellObject type){
        this(module,obj,type,new HashSet<HaskellEntity>());
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
            if (hv.guardPatDeclMembers(this)){
            this.subEntities = this.listWalk(this.subEntities,hv);
            }
        }
        return hv.caseEntity(this);
    }

    @Override
    public Set<HaskellEntity> getSubEntities(){
        return this.subEntities;
    }

    public void addSubEntity(HaskellEntity e){
        this.subEntities.add(e);
    }


}
