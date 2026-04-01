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
 * @author Marcel Klinzing
 */

public class PolyShapeQuadratic<C extends SemiRing<C>> extends IDPExportable.IDPExportableSkeleton implements PolyShapeHeuristic<C>

{

    @Override
    public void export(StringBuilder sb, Export_Util eu, VerbosityLevel verbosityLevel) {
        sb.append("PolyQuadraticShape");
    }

    @Override
    public Triple<Polynomial<C>, Map<IVariable<C>, Boolean>, ConcurrentMap<Integer, VFISet<C>>> getShape(final PolyInterpretation<C> interpretation,
        final IFunctionSymbol<?> f) {

        final List<PolyVariable<C>> vars =
            new ArrayList<PolyVariable<C>>(f.getArity());
        final PolyFactory factory = interpretation.getFactory();

        final C one = interpretation.getRing().one();
        final Map<Monomial<C>, C> polyMap = new LinkedHashMap<Monomial<C>, C>();

        final Map<IVariable<C>, Boolean> varQuantifications =
            new LinkedHashMap<IVariable<C>, Boolean>();

        final CollectionMap<Integer, IVariable<C>> varToCoeffs = new CollectionMap<>();
        final Map<PolyVariable<C>, Map<PolyVariable<C>, BigInt>> coeffToMonomMap = new LinkedHashMap<>();

        int fArity = f.getArity();
        for (int i = 0; i < fArity; i++) {
            final IVariable<C> var =
                    interpretation.getVariableForFunctionSymbolArgument(f, i);
                varQuantifications.put(var, true);
                vars.add(var);
        }

        for (int i = -1; i < fArity; i++) {

            final IVariable<C> coeff = interpretation.getNextCoeff(f, i);
            varQuantifications.put(coeff, false);
            varToCoeffs.add(i, coeff);

            final Map<PolyVariable<C>, BigInt> monomialMap = new LinkedHashMap<PolyVariable<C>, BigInt>();
            monomialMap.put(coeff, BigInt.ONE);

            if (i >= 0) {
                PolyVariable<C> var = vars.get(i);
                monomialMap.put(var, BigInt.ONE);
            }
            coeffToMonomMap.put(coeff, monomialMap);
            polyMap.put(factory.createMonomial(one, ImmutableCreator.create(monomialMap)), one);

        }

        for (int i = 0; i < vars.size(); i++) {
            for (int j = 0; j <= i; j++) {
                final IVariable<C> coeff = interpretation.getNextCoeff(f, i, j);
                varQuantifications.put(coeff, false);
                varToCoeffs.add(i, coeff);
                varToCoeffs.add(j, coeff);

                final Map<PolyVariable<C>, BigInt> monomialMap = new LinkedHashMap<PolyVariable<C>, BigInt>();
                monomialMap.put(coeff, BigInt.ONE);

                PolyVariable<C> var1 = vars.get(i);
                PolyVariable<C> var2 = vars.get(j);
                if (var1 == var2) {
                    monomialMap.put(var1, BigInt.TWO);
                } else {
                    monomialMap.put(var2, BigInt.ONE);
                    monomialMap.put(var1, BigInt.ONE);
                }

                coeffToMonomMap.put(coeff, monomialMap);
                polyMap.put(factory.createMonomial(one, ImmutableCreator.create(monomialMap)), one);
            }
        }

        final ConcurrentMap<Integer, VFISet<C>> vfiMap = this.createVFI(interpretation, f, varToCoeffs, coeffToMonomMap);
        final Polynomial<C> poly = factory.create(one, ImmutableCreator.create(polyMap));

        return new Triple<Polynomial<C>, Map<IVariable<C>, Boolean>, ConcurrentMap<Integer, VFISet<C>>>(
            poly, varQuantifications, vfiMap);
    }

    private ConcurrentMap<Integer, VFISet<C>> createVFI(final PolyInterpretation<C> interpretation,
        final IFunctionSymbol<?> f,
        final CollectionMap<Integer, IVariable<C>> varToCoeffs,
        final Map<PolyVariable<C>, Map<PolyVariable<C>, BigInt>> coeffToMonomMap) {

        final PolyFactory factory = interpretation.getFactory();
        final ItpfFactory constraintFactory = interpretation.getConstraintFactory();
        final ConcurrentMap<Integer, VFISet<C>> vfiMap = new ConcurrentHashMap<Integer, VFISet<C>>();

        for (int i = -1; i < f.getArity(); i++) {

            final ItpfBoolPolyVar<C> incVar =
                interpretation.getNextLogVar(PolyInterpretation.V_f_i_PREFIX + f.getName() + "_" + i + "_inc");
            final ItpfBoolPolyVar<C> decVar =
                interpretation.getNextLogVar(PolyInterpretation.V_f_i_PREFIX + f.getName() + "_" + i + "_dec");
            Collection<IVariable<C>> coeffs = varToCoeffs.get(i);

            Set<ItpfAtom> incConditions = new LinkedHashSet<>();
            Set<ItpfAtom> decConditions = new LinkedHashSet<>();
            for (IVariable<C> coeff : coeffs) {

                final Polynomial<C> coeffPoly = factory.create(coeff);
                Map<PolyVariable<C>, BigInt> monomialMap = coeffToMonomMap.get(coeff);
                ConstraintType constraintForCoeff = ConstraintType.GE;


                if (monomialMap.keySet().size() > 2) {
                    //i.e., we have a multiplication of two different variables
                    constraintForCoeff = ConstraintType.EQ;
                }
                for (Map.Entry<PolyVariable<C>, BigInt> entry : monomialMap.entrySet()) {
                    PolyVariable<C> var = entry.getKey();
                    if (var != coeff) {
                        if (entry.getValue().compareTo(BigInt.TWO) >= 0) {
                            constraintForCoeff = ConstraintType.EQ;
                        }
                    }
                }

                incConditions.add(constraintFactory.createPoly(coeffPoly, constraintForCoeff, interpretation));

                decConditions.add(constraintFactory.createPoly(coeffPoly.negate(), constraintForCoeff, interpretation));
            }

            Itpf incCondition =
                constraintFactory.create(constraintFactory.createClause(incConditions, true, ITerm.EMPTY_SET));
            Itpf decCondition =
                constraintFactory.create(constraintFactory.createClause(decConditions, true, ITerm.EMPTY_SET));
            final VFISet<C> vfi = new VFISet<C>(incVar, incCondition, decVar, decCondition);

            vfiMap.put(i, vfi);
        }
        return vfiMap;
    }

    @Override
    public boolean applies(PolyInterpretation<C> interpretation) {
        return true;
    }
}
