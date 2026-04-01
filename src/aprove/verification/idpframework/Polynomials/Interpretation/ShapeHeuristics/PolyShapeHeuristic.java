/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Polynomials.Interpretation.ShapeHeuristics;

import java.util.*;
import java.util.concurrent.*;

import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


public interface PolyShapeHeuristic<C extends SemiRing<C>> extends IDPExportable {

    /**
     * @param interpretation
     * @param f
     * @return null for using default shape (like linear...) OR x: shape (X1,
     * X2, ...) y: quantifications for variables (true == universal, false == exist)
     * z: map position (0, 1, ...) -> flag forceEncode + constraint for
     * increasin / decreasing position z: map position (0, 1, ...) -> log
     * variables for increasing / decreasing position
     */
    public Triple<Polynomial<C>, Map<IVariable<C>, Boolean>, ConcurrentMap<Integer, VFISet<C>>> getShape(final PolyInterpretation<C> interpretation,
        final IFunctionSymbol<?> f);

    /**
     * @param interpretation
     * @return true iff heuristics supplies a shape for the idp problem
     */
    public boolean applies(PolyInterpretation<C> interpretation);


}
