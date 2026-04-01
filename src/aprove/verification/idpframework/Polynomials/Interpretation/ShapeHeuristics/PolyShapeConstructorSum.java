package aprove.verification.idpframework.Polynomials.Interpretation.ShapeHeuristics;

import java.util.*;
import java.util.concurrent.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
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
public class PolyShapeConstructorSum<C extends SemiRing<C>> extends IDPExportable.IDPExportableSkeleton implements Immutable, PolyShapeHeuristic<C> {

    private final ImmutableCollection<IFunctionSymbol<?>> constructorSymbols;

    public PolyShapeConstructorSum(final ImmutableCollection<IFunctionSymbol<?>> constructorSymbols) {
        this.constructorSymbols = constructorSymbols;
    }

    @Override
    public Triple<Polynomial<C>, Map<IVariable<C>, Boolean>, ConcurrentMap<Integer, VFISet<C>>> getShape(final PolyInterpretation<C> interpretation,
        final IFunctionSymbol<?> f) {
        if (this.constructorSymbols.contains(f)) {
            final List<PolyVariable<C>> vars =
                new ArrayList<PolyVariable<C>>(f.getArity());
            final PolyFactory factory = interpretation.getFactory();
            final C ring = interpretation.getRing();
            final C one = interpretation.getRing().one();
            final Map<Monomial<C>, C> polyMap = new LinkedHashMap<Monomial<C>, C>();

            final ConcurrentMap<Integer, VFISet<C>> vfiMap =
                new ConcurrentHashMap<Integer, VFISet<C>>();
            final Map<IVariable<C>, Boolean> varQuantifications =
                new LinkedHashMap<IVariable<C>, Boolean>();

            final VFISet<C> increasingVfi =
                this.createIncVFI(interpretation);

            for (int i = -1; i < f.getArity(); i++) {

                if (i >= 0) {
                    final Map<PolyVariable<C>, BigInt> monomialMap = new LinkedHashMap<PolyVariable<C>, BigInt>();

                    final IVariable<C> var =
                        interpretation.getVariableForFunctionSymbolArgument(f, i);
                    varQuantifications.put(var, true);
                    vars.add(var);

                    monomialMap.put(var, BigInt.ONE);

                    polyMap.put(
                        factory.createMonomial(
                            ring,
                            ImmutableCreator.create(monomialMap)),
                        one);
                } else {
                    polyMap.put(factory.emptyMonomial(ring), one);
                }

                vfiMap.put(i, increasingVfi);
            }

            final Polynomial<C> poly = factory.create(one, ImmutableCreator.create(polyMap));

            return new Triple<Polynomial<C>, Map<IVariable<C>, Boolean>, ConcurrentMap<Integer, VFISet<C>>>(
                poly, varQuantifications, vfiMap);
        } else {
            return null;
        }
    }

    private VFISet<C> createIncVFI(final PolyInterpretation<C> interpretation) {
        final ItpfBoolPolyVar<C> incVar = interpretation.getNextLogVar(PolyInterpretation.V_f_i_PREFIX);
        final ItpfBoolPolyVar<C> decVar = interpretation.getNextLogVar(PolyInterpretation.V_f_i_PREFIX);

        final ItpfFactory constraintFactory = interpretation.getConstraintFactory();
        final Itpf incCondition = constraintFactory.createTrue();
        final Itpf decCondition = constraintFactory.createFalse();

        final VFISet<C> vfi =
            new VFISet<C>(incVar, incCondition, decVar, decCondition);
        return vfi;
    }

    @Override
    public boolean applies(final PolyInterpretation<C> interpretation) {
        return true;
    }


    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        sb.append("PolyShapeConstructorSum");
    }
}
