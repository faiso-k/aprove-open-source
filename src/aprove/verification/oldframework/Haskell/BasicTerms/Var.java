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
 * XML-Bean
 */
public class Var extends Atom implements HaskellBean,HaskellExp,HaskellPat,HaskellImport,HaskellExport,BasicTerm,HaskellType {
    HaskellEntity.Sort sort;

    transient int subtermID=-1;

    /**
     * Var is a HaskellBean so it needs an empty Constructor
     * do not use it in other context
     */
    public Var(){
    }

    /**
     * this Constructor should be used cause the symbol is
     * essential for a variable
     */
    public Var(HaskellSym sym){
        super(sym);
        this.sort = HaskellEntity.Sort.VAR;
    }

    @Override
    public void setSubtermNumber(int num) {
        this.subtermID = num;
    }

    @Override
    public int getSubtermNumber() {
        return this.subtermID;
    }

    @Override
    public Object deepcopy(){
        Var v = new Var(Copy.deep(this.getSymbol()));
        v.sort = this.sort;
        v.setSubtermNumber(this.getSubtermNumber());
        return this.hoCopy(v);
    }

    public void setSort(HaskellEntity.Sort sort){
        this.sort = sort;
    }

    public HaskellEntity.Sort getSort(){
        return this.sort;
    }

    /**
     * direct sort setter for HaskellASTBuilder or HaskellFactory
     */
    @Override
    public void setQCNAME(){
        this.sort = HaskellEntity.Sort.VAR;
    }

    /**
     * direct sort setter for HaskellASTBuilder
     */
    public void setFBIND(){
        this.sort = HaskellEntity.Sort.FVAR;
    }

    /**
     * direct sort setter for HaskellASTBuilder or HaskellFactory
     */
    public void setTYPE(){
        this.sort = HaskellEntity.Sort.TYVAR;
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
     * if a variable is in an importlist (not hiding)
     * it matches only with the correct sort;
     */
    @Override
    public boolean matchFilter(HaskellEntity e){
        return ((e.getSort() == this.sort) && this.getSymbol().matchNQ(e));
    }

    /**
     * if this.sort is an fvar only matching entities which are fvars should be filtered
     * if this.sort is a var both fvar and var matching entities are filtered
     */
    @Override
    public boolean hidingFilter(HaskellEntity e){
        if ((this.sort == HaskellEntity.Sort.FVAR) && (e.getSort() != HaskellEntity.Sort.IVAR)) {
            return false;
        }
        return this.getSymbol().matchNQ(e);
    }

    /**
     * for Interface HaskellExport
     * @return entities which are export if this var appear in an export specification of given module
     */
    @Override
    public Set<HaskellEntity> getExportEntities(Module mod){
        return mod.getEntities(this.getSymbol(),this.sort);
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseAtom(this);
        hv.fcaseVar(this);
        this.setSymbol(this.walk(this.getSymbol(),hv));
        return hv.caseVar(this);
    }

    /**
     * (interface BasicTerm)
     */
    @Override
    public BasicTerm.Sort getBasicSort(){
        return BasicTerm.Sort.VAR;
    }

    /**
     * returns a new fresh Variable without a name
     * this function could only be used to create type variables
     * cause only type variables could be annonym.
     */
    public static Var createFreshVar(){
        return new Var(new HaskellSym());
    }

    @Override
    public String toString(){
        return "V"+this.getSymbol().toString();
    }
}
