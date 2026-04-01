package aprove.verification.idpframework.Polynomials.Interpretation.ShapeHeuristics;

import java.util.*;
import java.util.concurrent.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public class PolyShapeLinear<C extends SemiRing<C>> extends IDPExportable.IDPExportableSkeleton implements
        PolyShapeHeuristic<C> {

    @Override
    public boolean applies(final PolyInterpretation<C> interpretation) {
        return true;
    }

    @Override
    public Triple<Polynomial<C>, Map<IVariable<C>, Boolean>, ConcurrentMap<Integer, VFISet<C>>> getShape(final PolyInterpretation<C> interpretation,
        final IFunctionSymbol<?> f) {
        final List<PolyVariable<C>> vars =
            new ArrayList<PolyVariable<C>>(f.getArity());
        final PolyFactory factory = interpretation.getFactory();
        final ItpfFactory constraintFactory = interpretation.getConstraintFactory();
        final C one = interpretation.getRing().one();
        final Map<Monomial<C>, C> polyMap = new LinkedHashMap<Monomial<C>, C>();

        final ConcurrentMap<Integer, VFISet<C>> vfiMap =
            new ConcurrentHashMap<Integer, VFISet<C>>();
        final Map<IVariable<C>, Boolean> varQuantifications =
            new LinkedHashMap<IVariable<C>, Boolean>();


        for (int i = -1; i < f.getArity(); i++) {

            final IVariable<C> coeff = interpretation.getNextCoeff(f, i);
            varQuantifications.put(coeff, false);

            final Map<PolyVariable<C>, BigInt> monomialMap = new LinkedHashMap<PolyVariable<C>, BigInt>();
            monomialMap.put(coeff, BigInt.ONE);

            if (i >= 0) {
                final IVariable<C> var =
                    interpretation.getVariableForFunctionSymbolArgument(f, i);
                varQuantifications.put(var, true);
                vars.add(var);

                monomialMap.put(var, BigInt.ONE);
            }

            polyMap.put(factory.createMonomial(one, ImmutableCreator.create(monomialMap)), one);

            final ItpfBoolPolyVar<C> incVar = interpretation.getNextLogVar(PolyInterpretation.V_f_i_PREFIX + f.getName() + "_" + i + "_inc");
            final ItpfBoolPolyVar<C> decVar = interpretation.getNextLogVar(PolyInterpretation.V_f_i_PREFIX + f.getName() + "_" + i + "_dec");

            final Polynomial<C> coeffPoly = factory.create(coeff);
            final Itpf incCondition =
                constraintFactory.create(constraintFactory.createPoly(
                    coeffPoly, ConstraintType.GE, interpretation), true, ITerm.EMPTY_SET);
            final Itpf decCondition =
                constraintFactory.create(constraintFactory.createPoly(
                    coeffPoly.negate(), ConstraintType.GE, interpretation),
                    true, ITerm.EMPTY_SET);
            final VFISet<C> vfi =
                new VFISet<C>(incVar, incCondition, decVar, decCondition);

            vfiMap.put(i, vfi);
        }
        final Polynomial<C> poly = factory.create(one, ImmutableCreator.create(polyMap));

        return new Triple<Polynomial<C>, Map<IVariable<C>, Boolean>, ConcurrentMap<Integer, VFISet<C>>>(
            poly, varQuantifications, vfiMap);
    }

    @Override
    public void export(final StringBuilder sb, final Export_Util o, final VerbosityLevel verbosityLevel) {
        sb.append("PolyLinearShape");
    }

}
