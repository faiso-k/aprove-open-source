package aprove.verification.oldframework.Haskell.Substitutors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Utility.*;

 /**
 * @author Stephan Swiderski
 * @version $Id$
 *
 *
 */

public class AutoNameVarSubstitutor extends HaskellVisitor{

    Map<HaskellSym,HaskellObject> subs = new HashMap<HaskellSym,HaskellObject>();
    NameGenerator ng;
    Module module;

    public AutoNameVarSubstitutor(NameGenerator ng,Module module){
        this.ng = ng;
        this.module = module;
    }

    @Override
    public HaskellObject caseVar(Var var) {
        HaskellSym sym = var.getSymbol();
        HaskellObject rep = this.subs.get(sym);
        if (rep != null) {
            return Copy.deep(rep);
        } else {
           VarEntity ve = new TyVarEntity(this.ng.getNameFor(sym),this.module,null,null);
       rep = new Var(new HaskellNamedSym(ve));
       this.subs.put(sym,rep);
           return rep;
        }
    }
}
