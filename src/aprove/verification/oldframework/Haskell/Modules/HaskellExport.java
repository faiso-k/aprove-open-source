package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This Interface is implemented by all HaskellObjects which can occur
 * in the export list of module.
 *
 */
public interface HaskellExport extends HaskellObject {
    public Set<HaskellEntity> getExportEntities(Module mod);
}
