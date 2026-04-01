package aprove.verification.oldframework.Haskell.Syntax;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Utility.*;



/**
 * @author Stephan Swiderski
 * @version $Id$
 * InstPreFunction represents a Function in an instance declaration
 * it is created by the parser, later it is transformed to an InstFunction
 * while the SetSymbolEntityVisitor visits the modules
 */
public class InstPreFunction extends PreFunction {

    public InstPreFunction(HaskellSym sym,List <FuncDecl> fdecls){
        super(sym,fdecls);
    }

    public InstPreFunction(FuncDecl fd){
        super(fd);
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new InstPreFunction(Copy.deep(this.getSymbol()),Copy.deepCol(this.fdecls)));
    }

    @Override
    public HaskellObject createFunction(){
        Function func = (Function) super.createFunction();
        return new InstFunction(this.getSymbol(),func);
    }

}
