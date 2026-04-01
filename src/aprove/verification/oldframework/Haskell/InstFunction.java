package aprove.verification.oldframework.Haskell;

import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Utility.*;



/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * represents a instance variable (function) in an instance declaration
 * it contains the representing function
 */
public class InstFunction extends SymObject {

    Function func;

    /**
     * do not use this constructor, its only for bean convention
     */
    public InstFunction(){
    }

    /**
     * normal constructor
     */
    public InstFunction(HaskellSym sym,Function func){
        super(sym);
        this.func = func;
    }

    public void setEntityPer(EntityFrame ef){
        this.sym.setEntity(ef.getLocalEntity(this.getSymbol(),HaskellEntity.Sort.IVAR));
    }

    public Function getFunction(){
        return this.func;
    }

    public void setFunction(Function func){
        this.func = func;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new InstFunction(Copy.deep(this.getSymbol()),Copy.deep(this.func)));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseInstFunction(this);
        this.setSymbol(this.walk(this.getSymbol(),hv));
        this.func = this.walk(this.func,hv);
        return this;
    }

    /**
     * return the IVarEntity of this InstFunction
     */
    public HaskellEntity getMemberForInst(){
        return this.getSymbol().getEntity();
    }
}
