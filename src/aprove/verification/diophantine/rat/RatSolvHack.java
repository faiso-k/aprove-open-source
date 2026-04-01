package aprove.verification.diophantine.rat;

import aprove.strategies.Parameters.*;
import aprove.strategies.Util.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Monoids.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 *
 * @author bearperson
 * @version $Id$
 */
public class RatSolvHack {
    private static <C extends GPolyCoeff> void setStuff(OPCSolver<C> solver, Ring<C> ringC) {
        CMonoid<GMonomial<GPolyVar>> monoid = new GMonomialMonoid<GPolyVar>();
        Ring<GPoly<C, GPolyVar>> polyFactory = new FullSharingFactory<C, GPolyVar>();

        GPolyFlatRing<C, GPolyVar> flatRing =
            new SimpleGPolyFlatRing<C, GPolyVar>(ringC, monoid);
        FlatteningVisitor<C, GPolyVar> inner = new FlatteningVisitor<C, GPolyVar>(flatRing);

        GPolyFlatRing<GPoly<C, GPolyVar>, GPolyVar> flatRing2 =
            new SimpleGPolyFlatRing<GPoly<C, GPolyVar>,
                GPolyVar>(polyFactory, monoid);
        FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> outer =
            new FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar>(
                    flatRing2);

        solver.setFvInner(inner);
        solver.setFvOuter(outer);
        solver.setPolyRing(polyFactory);
    }

    @SuppressWarnings("unchecked")
    private static <T extends GPolyCoeff> OPCSolver<T> getSolver(String strategyArg) {
        ParamValue value = StrategyTranslator.value(strategyArg);
        try {
            return (OPCSolver<T>) value.get(StrategyTranslator.standardProgram());
        } catch (WrappedParamMgrException e) {
            throw new RuntimeException(e);
        }
    }

    public static OPCSolver<MbyN> getMbyNSolver(String satBackend, boolean fixDenominator) {
        OPCSolver<MbyN> result;
        // String stolen from defaults.properties. Why isn't this included automatically?
        result = RatSolvHack.getSolver("MBYNTOFORMULA[Solver = SAT[SatConverter = PLAIN, SatBackend = " + satBackend + ", Simplification = MAXIMUM, SimplifyAll = True, StripExponents = False], " +
                (fixDenominator ? "FixDenominator=True]" : "FixDenominator=False]"));
        RatSolvHack.setStuff(result, new MbyNRing());
        return result;
    }

    public static OPCSolver<PoT> getPoTSolver(String satBackend) {
        OPCSolver<PoT> result;
        result = RatSolvHack.getSolver("RATTOFORMULA[SatBackend = " + satBackend + "]");
        RatSolvHack.setStuff(result, new PoTRing());
        return result;
    }
}
