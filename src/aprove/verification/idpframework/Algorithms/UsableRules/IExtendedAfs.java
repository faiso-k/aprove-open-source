package aprove.verification.idpframework.Algorithms.UsableRules;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Polynomials.*;

/**
 * @author MP
 */
public interface IExtendedAfs {

    RelDependency evaluateContext(IActiveCondition context);

    RelDependency filterPosition(IFunctionSymbol<?> f, int i);
}
