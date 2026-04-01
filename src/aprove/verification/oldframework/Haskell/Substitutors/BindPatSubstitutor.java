package aprove.verification.oldframework.Haskell.Substitutors;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Patterns.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 */

public class BindPatSubstitutor extends HaskellVisitor{

    @Override
    public HaskellObject caseBindPat(BindPat bp){
        return bp.getVariable();
    }

}
