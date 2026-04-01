package aprove.verification.complexity.Utility;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;
import java.util.logging.*;

import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

public class SanityChecks {


    private static final Logger log = Logger.getLogger("aprove.src.Complexity.Utility.SanityChecks");

    /**
     * Flattens the interpretations of function symbols.
     */
    public static void flatten(GInterpretation<BigIntImmutable> interp) {
        for (OrderPoly<BigIntImmutable> poly : interp.getPol().values()) {
            if (!poly.isFlat(interp.getOuterRingMonoid())) {
                interp.getFvOuter().applyTo(poly);
            }
            Map<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> monomials =
                poly.getMonomials(interp.getOuterRingMonoid());
            for (GPoly<BigIntImmutable, GPolyVar> coeff : monomials.values()) {
                interp.getFvInner().applyTo(coeff);
            }
        }
    }
    /**
     * Checks that interpretations of all function symbols not in definedSymbols
     * are strongly linear.
     *
     * If allowFiltering is set, zero-valued coefficients are also allowed.
     */
    public static boolean constructorSymbolsStronglyLinear(
            GInterpretation<BigIntImmutable> interp,
            Set<FunctionSymbol> definedSymbols,
            boolean allowFiltering) {
        Map<FunctionSymbol, OrderPoly<BigIntImmutable>> polInterpMap =
            interp.getPol();
        LinkedHashSet<FunctionSymbol> constructorSymbols =
            new LinkedHashSet<FunctionSymbol>(polInterpMap.keySet());
        constructorSymbols.removeAll(definedSymbols);

        for (FunctionSymbol cs : constructorSymbols) {
            OrderPoly<BigIntImmutable> poly =
                polInterpMap.get(cs);
            ImmutableMap<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> monomials =
                poly.getMonomials(interp.getOuterRingMonoid());
            for (Map.Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> e : monomials.entrySet()) {
                if (e.getKey().getExponents().size() == 0) {
                    // Skip constant part
                    continue;
                }

                GPoly<BigIntImmutable, GPolyVar> coeff = e.getValue();
                BigIntImmutable constPartI =
                    coeff.getConstantPart(interp.getInnerRingMonoid());
                BigInteger constPart = constPartI.getBigInt();

                boolean empty = coeff.getVariables().isEmpty();
                boolean ok = (empty
                        && (constPart.equals(BigInteger.ONE)
                                || (allowFiltering && constPart.equals(BigInteger.ZERO))));
                if (!ok) {
                    return SanityChecks.error("Constructor symbol " + cs +
                            " has no strongly linear interpretation:" +
                            GPolyTools.format(interp, poly));
                }
            }
        }
        return true;
    }

    /**
     * Checks if the interpretation fulfills the monotonicity requirements.
     */
    public static boolean isStronglyMonotone(GInterpretation<BigIntImmutable> interp,
            Map<FunctionSymbol, BitSet> monotoneRequirements) {
        for (Map.Entry<FunctionSymbol, BitSet> e : monotoneRequirements.entrySet()) {
            FunctionSymbol fs = e.getKey();
            BitSet monPos = e.getValue();
            OrderPoly<BigIntImmutable> poly = interp.getPol().get(fs);

            if (poly == null) {
                return SanityChecks.error("isStronglyMonotone: " + fs + " has no interpretation.");
            }

            /* Remove monomials where the variable part consists of none or two or more variables */
            Map<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> monomials =
                new LinkedHashMap<GMonomial<GPolyVar>, GPoly<BigIntImmutable,GPolyVar>>(
                        poly.getMonomials(interp.getOuterRingMonoid()));
            Iterator<Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>>> monomialsIt =
                monomials.entrySet().iterator();
            while (monomialsIt.hasNext()) {
                Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> monomialE =
                    monomialsIt.next();
                GMonomial<GPolyVar> monomialVar = monomialE.getKey();

                if (monomialVar.getExponents().size() != 1) {
                    monomialsIt.remove();
                }
            }

            for (int i = monPos.nextSetBit(0); i >= 0; i = monPos.nextSetBit(i+1)) {
                boolean hasPositiveCoeff = false;
                GPolyVar argVar = interp.getVariableForFunctionSymbolArgument(i);
                for (Map.Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> monomialE : monomials.entrySet()) {
                    GMonomial<GPolyVar> monomialVar = monomialE.getKey();
                    GPoly<BigIntImmutable, GPolyVar> monomialCoeff = monomialE.getValue();

                    /* We have ensured above, that there is exactly one exponent */
                    GPolyVar var = monomialVar.getExponents().keySet().iterator().next();
                    if (!var.equals(argVar)) {
                        continue;
                    }

                    BigInteger coeff = monomialCoeff.getConstantPart(interp.getInnerRingMonoid()).getBigInt();
                    if (coeff.signum() < 0) {
                        return SanityChecks.error("isStronglyMonotone: " + fs + ": " + GPolyTools.format(interp, poly)
                                + " has negative coefficient.");
                    } else if (coeff.signum() > 0) {
                        hasPositiveCoeff = true;
                    }
                }

                if (!hasPositiveCoeff) {
                    return SanityChecks.error("isStronglyMonotone: " + fs + ": " + GPolyTools.format(interp, poly)
                            + " is not monotone in the argument " + i + ".");
                }
            }
        }

        return true;
    }

    private static boolean error(String msg) {
        SanityChecks.log.warning(msg + "\n");
        return false;
}

    public static class NotSaneException extends RuntimeException {

        public NotSaneException(String e) {
            super(e);
        }

    }

}
