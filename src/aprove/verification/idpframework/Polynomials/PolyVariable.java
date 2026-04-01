package aprove.verification.idpframework.Polynomials;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 *
 * @author Martin Pluecker
 */
public interface PolyVariable<C extends SemiRing<C>> extends HasName,
 IDPExportable, XmlExportable {

    public boolean isMax();
    public boolean isRealVar();
    public C getRing();

}