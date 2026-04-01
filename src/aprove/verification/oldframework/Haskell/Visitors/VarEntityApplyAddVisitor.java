package aprove.verification.oldframework.Haskell.Visitors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Utility.*;

 /**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * replaces vars by a term containing the same var
 *
 * if a VarEntity ve is the subs map
 * the Variable Var(sym(ve)) is replaced by the term (Var(rsym) ro1 ro2 ... ron)
 * if [rsym ro1 ... ron] is the replace map value in the subs map
 * i.e.
 * the typeterm of each replace variable is adapted and ro1 .. rom are the ne parameters
 * and rsym is the new name of these variables
 */

public class VarEntityApplyAddVisitor extends HaskellVisitor{
    Map<? extends HaskellEntity,List<HaskellObject>> subs;
    Prelude prelude;

    public VarEntityApplyAddVisitor(Prelude prelude,Map<? extends HaskellEntity,List<HaskellObject>> subs){
        this.subs = subs;
        this.prelude = prelude;
    }

    @Override
    public HaskellObject caseVar(Var var) {
        HaskellEntity e = var.getSymbol().getEntity();
        List<HaskellObject> rep = this.subs.get(e);
        if (rep != null) {
            rep = Copy.deepCol(rep);
            HaskellSym sym = (HaskellSym)rep.remove(0);
            var.setSymbol(sym);
            var.setTypeTerm(this.prelude.buildArrows(HaskellTools.getTypeTerms(rep),var.getTypeTerm()));
            return this.prelude.buildApplies(var,rep);

        } else {
            return var;
        }
    }

}
