package aprove.verification.oldframework.Haskell.Modules;

import aprove.verification.oldframework.Haskell.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This interface is implemented by all HaskellObjects which can occur
 * in an import sepcification (hiding or non hiding)
 */
public interface HaskellImport extends HaskellObject {

    public boolean matchFilter(HaskellEntity e);
    public boolean hidingFilter(HaskellEntity e);

}
