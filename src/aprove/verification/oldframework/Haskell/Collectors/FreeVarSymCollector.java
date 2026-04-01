package aprove.verification.oldframework.Haskell.Collectors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Typing.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This visitor collects free variable symbols in a HaskellObject,
 * In a typeschema the quantor blocks variable symbols from being picked up
 * entityframes or other stuff is ignored
 */
public class FreeVarSymCollector extends HaskellVisitor{
    Quantor quantor;
    Collection<HaskellSym> col;

    public FreeVarSymCollector(Collection<HaskellSym> col){
        this.col = col;
        this.quantor = null;
    }

    @Override
    public void fcaseVar(Var var) {
        HaskellSym sym = var.getSymbol();
        if (this.quantor != null) {
            if (this.quantor.contains(sym)) {
                return;
            }
        }
        this.col.add(sym);
    }

    @Override
    public void fcaseTypeSchema(TypeSchema ts){
        this.quantor = ts.getQuantor();
    }

    @Override
    public HaskellObject caseTypeSchema(TypeSchema ts){
        this.quantor = null;
        return ts;
    }

    public static Set<HaskellSym> applyTo(HaskellObject ho){
        Set<HaskellSym> fvss = new HashSet<HaskellSym>();
        ho.visit(new FreeVarSymCollector(fvss));
        return fvss;
    }

}
