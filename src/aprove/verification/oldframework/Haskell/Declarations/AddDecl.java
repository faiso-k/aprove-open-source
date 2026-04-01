package aprove.verification.oldframework.Haskell.Declarations;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * All classes that implement this interface carry additional informations
 * for a haskell entity, i.e.: InfixDecl and TypeDecl implement this interface
 */
public interface AddDecl extends HaskellObject {
    public void transferTo(EntityMap entities);
}



