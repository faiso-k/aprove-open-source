package aprove.verification.idpframework.Polynomials.Interpretation.ShapeHeuristics;

import java.util.*;
import java.util.concurrent.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class PolyShapeChain<C extends SemiRing<C>> extends IDPExportable.IDPExportableSkeleton implements Immutable, PolyShapeHeuristic<C> {

    private final ImmutableList<PolyShapeHeuristic<C>> heuristics;

    public PolyShapeChain(final ImmutableList<PolyShapeHeuristic<C>> heuristics) {
        this.heuristics = heuristics;
    }

    @Override
    public Triple<Polynomial<C>, Map<IVariable<C>, Boolean>, ConcurrentMap<Integer, VFISet<C>>> getShape(final PolyInterpretation<C> interpretation,
        final IFunctionSymbol<?> f) {
        for (final PolyShapeHeuristic<C> heuristic : this.heuristics) {
            if (heuristic.applies(interpretation)) {
                final Triple<Polynomial<C>, Map<IVariable<C>, Boolean>, ConcurrentMap<Integer, VFISet<C>>> polyShape =
                    heuristic.getShape(interpretation, f);
                if (polyShape != null) {
                    return polyShape;
                }
            }
        }

        return null;
    }

    @Override
    public boolean applies(final PolyInterpretation<C> interpretation) {
        for (final PolyShapeHeuristic<C> heuristic: this.heuristics) {
            if (heuristic.applies(interpretation)) {
                return true;
            }
        }

        return false;
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        sb.append(eu.escape("PolyShapeChain ["));
        final Iterator<PolyShapeHeuristic<C>> iterator = this.heuristics.iterator();
        while(iterator.hasNext()) {
            iterator.next().export(sb, eu, verbosityLevel);
            if (iterator.hasNext()) {
                sb.append(eu.escape(", "));
            }
        }

        sb.append(eu.escape("]"));
    }

}
