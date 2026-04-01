package aprove.verification.oldframework.Haskell.Collectors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This visitor collects local free variable symbols in a HaskellObject,
 * In a typeschema the quantor blocks variable symbols from being picked up
 * entityframes or other stuff is ignored
 */
public class FreeLocalVarSymCollector extends FreeVarSymCollector {

    public FreeLocalVarSymCollector(Collection<HaskellSym> col){
        super(col);
    }

    @Override
    public void fcaseVar(Var var) {
        HaskellSym sym = var.getSymbol();
        VarEntity varEnt = (VarEntity)sym.getEntity();
        if ( (varEnt == null) || (varEnt.getLocal()) ) {
            super.fcaseVar(var);
        }
    }

}
