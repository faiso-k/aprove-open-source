package aprove.verification.idpframework.Algorithms.Filter;

import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public interface IDPFilterHeuristic extends IDPExportable {

    /**
     * @param interpretation
     * @param f
     */
    public ImmutableCollection<Integer> getFilteredPositions(IDependencyGraph graph,
        IFunctionSymbol<?> f);

}
