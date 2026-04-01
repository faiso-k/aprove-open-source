package aprove.verification.oldframework.Haskell.Substitutors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Utility.*;

 /**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * AutoRenVarSubstitutor renames all variables in the visited HaskellObject
 * in fresh ones, if a variable is used more then once in a HaskellObject
 * then it will be replaced at each occurens with the same new variable
 * only for !!TypeTerms!! cause of using Var.createFreshVar
 */

public class AutoRenVarSubstitutor extends HaskellVisitor{

    Map<HaskellSym,HaskellObject> subs = new HashMap<HaskellSym,HaskellObject>();

    @Override
    public HaskellObject caseVar(Var var) {
        HaskellSym sym = var.getSymbol();
        HaskellObject rep = this.subs.get(sym);
        if (rep != null) {
            return Copy.deep(rep);
        } else {
       rep = Var.createFreshVar();
       this.subs.put(sym,rep);
           return rep;
        }
    }
}
