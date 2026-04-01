package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * ConsExport represents the entry in a export specification of the form
 * <code>TyCons(....)</code> or <code> TyCons(C1,...,CN) </code>
 */
public class ConsExport extends HaskellObject.HaskellObjectSkeleton implements HaskellBean, HaskellExport {
    Cons cons;
    List<Atom> atoms;  // List of constructors, if atoms = null all constructors are exported

    /**
     * do not use this constructor, its only for bean convention
     */
    public ConsExport(){
    }

    /**
     * normal constructor
     */
    public ConsExport(Cons cons, List<Atom> atoms){
        this.cons = cons;
        this.atoms = atoms;
    }

    public List<Atom> getAtoms(){
        return this.atoms;
    }

    public void setAtoms(List<Atom> atoms){
        this.atoms = atoms;
    }

    public Cons getCons(){
        return this.cons;
    }

    public void setCons(Cons cons){
        this.cons = cons;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new ConsExport(Copy.deep(this.cons),Copy.deepCol(this.atoms)));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        this.cons = this.walk(this.cons,hv);
        this.atoms = this.listWalk(this.atoms,hv);
        return this;
    }

    /**
     * Interface HaskellExport
     * @returns the export entities meant by this export entry
     */
    @Override
    public Set<HaskellEntity> getExportEntities(Module mod){
        Set<HaskellEntity> res= new HashSet<HaskellEntity>();
        Set<HaskellEntity> par = mod.getEntities(this.cons.getSymbol(),HaskellEntity.Sort.TYCLASS);
        par.addAll(mod.getEntities(this.cons.getSymbol(),HaskellEntity.Sort.TYCONS));
        if (this.atoms == null) { // means the case (..)
            for (HaskellEntity e : par){
                res.addAll(e.getSubEntities());
            }
        } else {
            for (Atom a : this.atoms){
                res.addAll(a.getExportEntities(mod));
            }
        }
        res.addAll(par);
        return res;
    }
}
