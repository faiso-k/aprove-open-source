package aprove.verification.oldframework.Haskell.Collectors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This visitor collects all occuring constructor symbols in a HaskellObject
 * for each occuring symbol is added to the collection even if it contains it already
 */
public class ConsSymCollector extends HaskellVisitor{
    Collection<HaskellSym> col;

    public ConsSymCollector(Collection<HaskellSym> col){
        this.col = col;
    }

    @Override
    public void fcaseCons(Cons cons) {
        HaskellSym sym = cons.getSymbol();
        this.col.add(sym);
    }

    public static Set<HaskellSym> applyTo(HaskellObject ho){
        Set<HaskellSym> fvss = new HashSet<HaskellSym>();
        ho.visit(new ConsSymCollector(fvss));
        return fvss;
    }

}
