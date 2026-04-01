package aprove.verification.idpframework.Core.Utility;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.SemiRings.*;

/**
 *
 * @author MP
 */
public interface HasRootSymbol<T extends SemiRing<T>> {

    public IFunctionSymbol<T> getRootSymbol();

}
