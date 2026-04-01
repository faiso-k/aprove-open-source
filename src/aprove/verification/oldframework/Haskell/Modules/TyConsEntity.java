package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * TyConsEntity is the intern representation of data (or newtype) declarations
 * it represents a type constructor and contains a list of
 * the data constructors.
 */

public class TyConsEntity extends HaskellEntity.TypeSkeleton implements EntityCollector {
    List<ConsEntity> consList;
    boolean newType;

    /**
     * do not use this constructor, its only for bean convention
     */
    public TyConsEntity(){
    }

    /**
     * constructor for deepcopy
     */
    public TyConsEntity(String name,Module module,DataDecl dd,List<ConsEntity> consList){
        super(name,HaskellEntity.Sort.TYCONS,module,dd);
        this.setFixity(InfixDecl.FIXITY_DEFAULT);
        this.setPriority(InfixDecl.PRIORITY_DEFAULT);
        this.consList = consList;
        if (dd == null) {
            this.newType = false;
        } else {
            this.newType = dd.getNewType();
        }
    }

    /**
     * normal constructor
     */
    public TyConsEntity(String name,Module module,DataDecl dd){
        this(name,module,dd,new Vector<ConsEntity>());
    }

    @Override
    public Set<HaskellEntity> getSubEntities(){
        Set<HaskellEntity> res = new HashSet<HaskellEntity>();
        for (ConsEntity con : this.consList) {
            if (con.getSelectors() != null) {
                for (Var sel : con.getSelectors()) {
                    res.add(sel.getSymbol().getEntity());
                }
            }
        }
        res.addAll(this.consList);
        return res;
    }

    /**
     * adds a ConsEntity to this TyConsEntity
     * and to the Module of this TyConsEntity
     */
    public void addCons(ConsEntity e){
        this.consList.add(e);
        this.module.addLinkEntity(e);
        e.setParentEntity(this);
    }

    /**
     * This Methode should do really nothing, it satisfies only the Collector interface
     * addCons is the proper function, cause an EntityMap is unordered.
     * This is a TyConsEntity and it needs the order of the ConsEntities.
     */
    @Override
    public void setCollectedEntities(EntityMap em){
    }

    @Override
    public Set<HaskellEntity> getCollectedEntities(){
        return this.getSubEntities();
    }

    public boolean getNewType(){
        return this.newType;
    }

    public void setNewType(boolean newType){
        this.newType = newType;
    }

    public List<ConsEntity> getConsList(){
        return this.consList;
    }

    public void setConsList(List<ConsEntity> consList){
        this.consList = consList;
    }

    @Override
    public void addEntity(HaskellEntity e){
        throw new RuntimeException("addEntity is not supported");
    }

    @Override
    public void removeEntity(HaskellEntity e){
        throw new RuntimeException("removeEntity is not supported");
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
                this.consList = this.listWalk(this.consList,hv);
            }
        }
        return hv.caseEntity(this);
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new TyConsEntity(this.name,this.module,(DataDecl) Copy.deep(this.getValue()),
                  new Vector<ConsEntity>(this.consList)));
    }

}
