package aprove.verification.oldframework.Haskell.Syntax;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Utility.*;



/**
 * @author Stephan Swiderski
 * @version $Id$
 * The PreFunction represents a Haskell-Function and is created by the Parser
 * later it is transformed to a Function while the SetSymbolEntityVisitor visits the modules
 * it collects all FuncDecls of a function
 */
public class PreFunction extends SymObject {

    List<FuncDecl> fdecls;
    boolean solo = true;

    public PreFunction(HaskellSym sym,List <FuncDecl> fdecls){
        super(sym);
        this.fdecls = fdecls;
    }

    public PreFunction(FuncDecl fd){
        super(fd.getFunction());
        this.fdecls = new Vector<FuncDecl>();
        this.fdecls.add(fd);
        this.solo = fd.isSolitary();
    }

    public void setEntity(HaskellEntity e){
        this.getSymbol().setEntity(e);
    }

    /**
     * If a FuncDecl matches the symbol it is added to this PreFunction
     */
    public boolean matchAdd(FuncDecl fd){
        if (this.solo || fd.isSolitary()) {
            return false;
        }
        HaskellSym sym = fd.getFunction();
        if (sym.matchNQ(this.getSymbol())){
           this.fdecls.add(fd);
           sym.setEntity(this.getSymbol().getEntity());
           return true;
        }
        return false;
    }

    @Override
    public Object deepcopy(){
        PreFunction pf = new PreFunction(this.getSymbol(),Copy.deepCol(this.fdecls));
        pf.solo = this.solo;
        return this.hoCopy(pf);
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcasePreFunction(this);
        this.setSymbol(this.walk(this.getSymbol(),hv));
        this.fdecls = this.listWalk(this.fdecls,hv);
        return hv.casePreFunction(this);
    }

    public HaskellObject createFunction(){
        List<HaskellRule> rules = new Vector<HaskellRule>();
        for (FuncDecl fd : this.fdecls){
            rules.add(fd.createRule());
        }
        return (new Function(this.getSymbol(),rules)).transferToken(this);
    }

}
