package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 * ConsImport represents the entry in an import specification of the form
 * <code>TyCons(..)</code> or <code> TyCons(C1,..,CN) </code>
 */
public class ConsImport extends HaskellObject.HaskellObjectSkeleton implements HaskellBean, HaskellImport {
    Cons cons;
    List<Atom> atoms; // atoms == null semantic of (..) in Cons(..)

    /**
     * do not use this constructor, its only for bean convention
     */
    public ConsImport(){
    }

    /**
     * normal constructor
     */
    public ConsImport(Cons cons, List<Atom> atoms){
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
        return this.hoCopy(new ConsImport(Copy.deep(this.cons),Copy.deepCol(this.atoms)));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        this.cons = this.walk(this.cons,hv);
        this.atoms = this.listWalk(this.atoms,hv);
        return this;
    }

    /**
     * checks if an entity matches to this import statement
     * @returns true, iff the entity is imported by this import
     */
    @Override
    public boolean matchFilter(HaskellEntity e){
        if ((HaskellEntity.Sort.TYCS.contains(e.getSort())) && this.cons.getSymbol().matchNQ(e)){
            return true;
        } else if ((e.getSort() == HaskellEntity.Sort.CONS) || (e.getSort() == HaskellEntity.Sort.VAR)){
            if (this.atoms == null) {
                return this.matchFilter(e.getParentEntity());
            } else {
               for (Atom a : this.atoms){
                  if (a.matchFilter(e)) {
                    return true;
                }
               }
            }
        }
        return false;
    }

    /**
     * checks if an entity matches to this import statement
     * @returns true, iff the entity is hidden by this import
     */
    @Override
    public boolean hidingFilter(HaskellEntity e){

        if (e == null) {
            return false;
        }

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("CheckHidingcoimp "+this.cons.getSymbol().getName(false)+" --- "+e.getName());
        }

        if ((HaskellEntity.Sort.TYCS.contains(e.getSort())) && this.cons.getSymbol().matchNQ(e)){
            return true;
        } else if ((e.getSort() == HaskellEntity.Sort.CONS) || (e.getSort() == HaskellEntity.Sort.VAR)){
            if (this.atoms == null) {
                return this.hidingFilter(e.getParentEntity());
            } else {
                for (Atom a : this.atoms){
                    if (a.hidingFilter(e)) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

}
