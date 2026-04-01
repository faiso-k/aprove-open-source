package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;
/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The TyVarTransformerVisitor replaces named type-variables with
 * new unamed one
 * for each name one unamed variable is created
 */

public class TyVarTransformerVisitor extends HaskellVisitor{
    Map<HaskellEntity,HaskellSym> replacement;

    public TyVarTransformerVisitor(){
        this.replacement = new HashMap<HaskellEntity,HaskellSym>();
    }

    @Override
    public HaskellObject caseVar(Var var) {
        HaskellEntity e = var.getSymbol().getEntity();
        HaskellSym sym = this.replacement.get(e);
        if (sym == null) {
            sym = new HaskellSym();
            this.replacement.put(e,sym);
        }
        return new Var(sym);
    }

    public Quantor getQuantor(){
        return new Quantor(new HashSet<HaskellSym>(this.replacement.values()));
    }

}
