package aprove.verification.oldframework.Haskell.BasicTerms;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * Cons is the constructor atom of Haskell in types, patterns and expressions
 * XML-Bean
 */
public class Cons extends Atom implements HaskellBean,HaskellExp,HaskellPat,HaskellImport,HaskellExport,BasicTerm,HaskellType {

    HaskellEntity.Sort sort;

    transient int subtermID=-1;


    /**
     * Cons is a HaskellBean so it needs an empty Constructor
     * do not use it in other context
     */
    public Cons(){
    }

    /**
     * this Constructor should be used cause the symbol is
     * essential for a constructor
     */
    public Cons(HaskellSym sym){
        super(sym);
        this.sort = HaskellEntity.Sort.CONS;
    }

    @Override
    public void setSubtermNumber(int num) {
        this.subtermID = num;
    }

    @Override
    public int getSubtermNumber() {
        return this.subtermID;
    }

    public void setSort(HaskellEntity.Sort sort){
        this.sort = sort;
    }

    public HaskellEntity.Sort getSort(){
        return this.sort;
    }

    @Override
    public Object deepcopy(){
        Cons c = new Cons(Copy.deep(this.getSymbol()));
        c.sort = this.sort;
        c.setSubtermNumber(this.getSubtermNumber());
        return this.hoCopy(c);
    }

    /**
     * see abstract class Atom
     */
    @Override
    public void setEntityPer(EntityFrame ef){
        if (this.getSymbol().getEntity() == null) {
            this.getSymbol().setEntityPer(ef,this.sort);
        }
    }

    /**
     * direct sort setter for HaskellFactory or HaskellASTBuilder
     */
    public void setTYCLASS(){
        this.sort = HaskellEntity.Sort.TYCLASS;
    }

    /**
     * direct sort setter for HaskellFactory or HaskellASTBuilder
     */
    public void setTYCONS(){
        this.sort = HaskellEntity.Sort.TYCONS;
    }

    /**
     * direct sort setter for HaskellFactory or HaskellASTBuilder
     */
    public void setTYPE(){
        this.sort = HaskellEntity.Sort.TYCONS;
    }

    /**
     * direct sort setter for HaskellFactory or HaskellASTBuilder
     */
    @Override
    public void setQCNAME(){
        this.sort = HaskellEntity.Sort.CONS;
    }

    @Override
    public boolean matchFilter(HaskellEntity e){
        return ((e.getSort() == this.sort) && this.getSymbol().matchNQ(e));
    }

    /**
     * @return true
     *  if this.sort is CONS and the entity has sort CONS and has the same name
     *  or if this.sort is not CONS and the parent entity of the given entity has the same name
     */
    @Override
    public boolean hidingFilter(HaskellEntity e){

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("CheckHiding "+this.getSymbol().getName(false)+"-"+this.sort+" --- "+e.getName());
        }

        if ((this.sort == HaskellEntity.Sort.CONS)){
            if (e.getSort() != HaskellEntity.Sort.CONS) {
                return false;
            }
            return (this.getSymbol().matchNQ(e));
        } else {
            if (this.getSymbol().matchNQ(e)) {
                return true;
            }
            if ((e.getSort() == HaskellEntity.Sort.CONS)) {
                return (this.hidingFilter(e.getParentEntity()));
            }
            return false;
        }
    }

    /**
     * for Interface HaskellExport
     * @return entities which are export if this cons appear in an export specification of given module
     */
    @Override
    public Set<HaskellEntity> getExportEntities(Module mod){
        return mod.getEntities(this.getSymbol(),this.sort);
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseAtom(this);
        hv.fcaseCons(this);
        this.setSymbol(this.walk(this.getSymbol(),hv));
        return hv.caseCons(this);
    }

    /**
     * (interface BasicTerm)
     */
    @Override
    public BasicTerm.Sort getBasicSort(){
        return BasicTerm.Sort.CONS;
    }

    @Override
    public String toString(){
        return "C"+this.getSymbol().toString();
    }

}
