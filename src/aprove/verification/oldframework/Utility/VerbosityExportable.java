package aprove.verification.oldframework.Utility;

import aprove.prooftree.Export.Utility.*;

/**
 * Created on 30.05.2005 by marmer
 *
 * New interface which combines export with verbosity levels. It
 * extends Exportable (without VerbosityLevel) which should be used
 * with the default verbosity level.
 *
 * @author marmer
 * @version $Id$
 */

public interface VerbosityExportable extends Exportable {

    public static VerbosityLevel DEFAULT_LEVEL = VerbosityLevel.MIDDLE;

    public String export(Export_Util o, VerbosityLevel level);

}
