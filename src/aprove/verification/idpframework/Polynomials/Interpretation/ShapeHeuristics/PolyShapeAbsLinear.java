package aprove.verification.idpframework.Polynomials.Interpretation.ShapeHeuristics;

import java.util.*;
import java.util.concurrent.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
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
 * @author Marcel Klinzing
 */
public class PolyShapeAbsLinear<C extends SemiRing<C>> extends IDPExportable.IDPExportableSkeleton implements
        PolyShapeHeuristic<C> {

    IDPProblem problem;
    public PolyShapeAbsLinear (IDPProblem problem) {
        this.problem = problem;
    }

    @Override
    public boolean applies(final PolyInterpretation<C> interpretation) {
        return true;
    }

    @Override
    public Triple<Polynomial<C>, Map<IVariable<C>, Boolean>, ConcurrentMap<Integer, VFISet<C>>> getShape(final PolyInterpretation<C> interpretation,
        final IFunctionSymbol<?> f) {

        Set<Integer> maxMap = this.maxHeuristic(this.problem, f);
        final List<PolyVariable<C>> vars =
            new ArrayList<PolyVariable<C>>(f.getArity());
        final PolyFactory factory = interpretation.getFactory();
        final C one = interpretation.getRing().one();

        final Map<IVariable<C>, Boolean> varQuantifications =
            new LinkedHashMap<IVariable<C>, Boolean>();

        final CollectionMap<Integer, IVariable<C>> varToCoeffs = new CollectionMap<>();
        final Set<PolyVariable<C>> absCoeffs = new LinkedHashSet<>();

        C zero = interpretation.getRing().zero();
        C minusOne = one.negate();

        Polynomial<C> poly =  factory.create(zero);

        for (int i = -1; i < 2*f.getArity(); i++) {

            final IVariable<C> coeff = interpretation.getNextCoeff(f, i);
            varQuantifications.put(coeff, false);

            final Map<PolyVariable<C>, BigInt> monomialMap = new LinkedHashMap<PolyVariable<C>, BigInt>();

            if (i >= 0 && i < f.getArity()) {
                varToCoeffs.add(i, coeff);
                final IVariable<C> var =
                        interpretation.getVariableForFunctionSymbolArgument(f, i);
                    varQuantifications.put(var, true);
                    vars.add(var);
                    monomialMap.put(coeff, BigInt.ONE);
                    monomialMap.put(var, BigInt.ONE);

                    poly = poly.add(factory.create(factory.createMonomial(one, ImmutableCreator.create(monomialMap)), one));

            } else if (i >= f.getArity()) {

                int nextArg = i - f.getArity();
                if (!maxMap.contains(nextArg)) {
                    continue;
                }
                varToCoeffs.add(nextArg, coeff);
                absCoeffs.add(coeff);

                final PolyVariable<C> var = vars.get(nextArg);
                    monomialMap.put(var, BigInt.ONE);
                    Polynomial<C> monomial = factory.create(coeff);
                    monomial = monomial.mult(factory.max(one,
                        factory.create(factory.createMonomial(one, ImmutableCreator.create(monomialMap)), one),
                        factory.create(factory.createMonomial(one, ImmutableCreator.create(monomialMap)), minusOne)));

                    poly = poly.add(monomial);

            } else {
                varToCoeffs.add(i, coeff);
                poly = poly.add(factory.create(coeff));
            }
        }



        final ConcurrentMap<Integer, VFISet<C>> vfiMap = this.createVFI(interpretation, f, varToCoeffs, absCoeffs);

        return new Triple<Polynomial<C>, Map<IVariable<C>, Boolean>, ConcurrentMap<Integer, VFISet<C>>>(
            poly, varQuantifications, vfiMap);
    }

        private ConcurrentMap<Integer, VFISet<C>> createVFI(final PolyInterpretation<C> interpretation,
            final IFunctionSymbol<?> f,
            final CollectionMap<Integer, IVariable<C>> varToCoeffs,
            final Set<PolyVariable<C>> absCoeffs) {

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
                    ConstraintType constraintForCoeff = ConstraintType.GE;


                    if (absCoeffs.contains(coeff)) {
                        constraintForCoeff = ConstraintType.EQ;
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

    /*
     * Where do we want to really use max?
     */
    private Set<Integer> maxHeuristic(IDPProblem problem, IFunctionSymbol<?> f) {

        IDependencyGraph graph = problem.getIdpGraph();
        Set<Integer> maxPos = new LinkedHashSet<>();

        for (INode node : graph.getNodes()) {

            if (graph.getNodeMap().get(node).getFunctionSymbols().contains(f)) {
                for (int i = 0; i < f.getArity(); i++) {
                    maxPos.add(i);
                }
            }
        }

        return maxPos;
    }

    @Override
    public void export(final StringBuilder sb, final Export_Util o, final VerbosityLevel verbosityLevel) {
        sb.append("PolyAbsoluteLinearShape");
    }

}
