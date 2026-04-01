package aprove.verification.oldframework.Haskell.Visitors;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Modules.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This visitor creates fresh unique names which are collected in the prelude.
 * see prelude.freshNameFor
 */

public class NameVisitor extends HaskellVisitor{
    Prelude prelude;

    public NameVisitor(Prelude prelude){
        this.prelude = prelude;
    }

    @Override
    public void fcaseHaskellNamedSym(HaskellNamedSym ho) {
        this.prelude.freshNameFor(ho);
    }

    @Override
    public boolean guardPatDeclSymbol(PatDecl ho)           { return true;}

}