package aprove.verification.oldframework.Haskell.Substitutors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Utility.*;

 /**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * replaces Variables with Symbols refering to a HaskellEntity in the given map
 * with the related value
 */
public class VarEntitySubstitutor extends HaskellVisitor{
    Map<? extends HaskellEntity,? extends HaskellObject> subs;

    public VarEntitySubstitutor(Map<? extends HaskellEntity,? extends HaskellObject> subs){
        this.subs = subs;
    }

    @Override
    public HaskellObject caseVar(Var var) {
        HaskellEntity e = var.getSymbol().getEntity();
        HaskellObject rep = this.subs.get(e);
        if (rep != null) {
            return Copy.deep(rep);
        } else {
            return var;
        }
    }

}
