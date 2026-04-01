package aprove.verification.dpframework.IDPProblem;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Utility.*;

/**
 *
 * @author Martin Pluecker
 */
public interface IDPExportable {

    public String export(Export_Util o, IDPPredefinedMap predefinedMap, VerbosityLevel verbosityLevel);

}
