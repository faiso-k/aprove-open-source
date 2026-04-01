package aprove.verification.idpframework.Core.PredefinedFunctions;

import java.math.*;
import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction.*;
import aprove.verification.idpframework.Core.SemiRings.*;

/**
 * @author Martin Pluecker
 */
public class PredefinedUtil {

    public static Boolean getBoolValue(final IFunctionSymbol<?> fs) {
        if (PredefinedSemanticsFactory.BOOLEAN_FS_TRUE.equals(fs)) {
            return true;
        } else if (PredefinedSemanticsFactory.BOOLEAN_FS_FALSE.equals(fs)) {
            return false;
        } else {
            return null;
        }
    }

    public static Boolean getBoolValue(final ITerm<?> t) {
        if (t.isVariable()) {
            return null;
        }
        if (PredefinedSemanticsFactory.BOOLEAN_TERM_TRUE.equals(t)) {
            return true;
        } else if (PredefinedSemanticsFactory.BOOLEAN_TERM_FALSE.equals(t)) {
            return false;
        } else {
            return null;
        }
    }

    public static <C extends IntRing<C>> C getIntValue(final IFunctionSymbol<C> fs,
        final SemiRingDomain<C> domain) {

        final PredefinedConstructor<C> constr =
            PredefinedUtil.getPredefinedConstructor(fs);

        if (constr != null && constr.getArity() == 0
            && constr.getResultDomain().equals(domain)) {
            return ((PfInt<C>) constr).getValue();

        } else {
            return null;
        }
    }

    public static <C extends IntRing<C>> C getIntValue(final ITerm<?> t,
        final SemiRingDomain<C> domain) {
        if (!t.isVariable() && t.getDomain().equals(domain)) {
            @SuppressWarnings("unchecked")
            final IFunctionSymbol<C> fs =
                ((IFunctionApplication<C>) t).getRootSymbol();
            return PredefinedUtil.getIntValue(fs, domain);
        }
        return null;
    }

    public static BigInt getIntValue(final String val,
        final IntegerDomain<BigInt> domain) {
        if (val.matches("-?\\d+")) {
            final BigInt value = BigInt.create(new BigInteger(val));
            if (domain.inRange(value)) {
                return value;
            } else {
                return null;
            }
        } else {
            return null;
        }
    }

    /**
     * Returns the pre-defined constroctor semantics of fs if present or null
     * @param fs
     * @return
     */
    public static <R extends SemiRing<R>> PredefinedConstructor<R> getPredefinedConstructor(final IFunctionSymbol<R> fs) {
        final PredefinedSemantics<R> semantics = fs.getSemantics();
        if (semantics != null && semantics.isConstructor()) {
            return (PredefinedConstructor<R>) semantics;
        } else {
            return null;
        }
    }

    /**
     * Returns the pre-defined function semantics of fs if present or null
     * @param fs
     * @return
     */
    public static <R extends SemiRing<R>> PredefinedFunction<?, R> getPredefinedFunction(final IFunctionSymbol<R> fs) {
        final PredefinedSemantics<R> semantics = fs.getSemantics();
        if (semantics != null && !semantics.isConstructor()) {
            return (PredefinedFunction<?, R>) semantics;
        } else {
            return null;
        }
    }

    public static <R extends IntRing<R>> boolean isInt(final IFunctionSymbol<?> fs,
        final SemiRingDomain<R> domain) {
        final PredefinedConstructor<?> constr =
            PredefinedUtil.getPredefinedConstructor(fs);

        return constr != null && constr.getArity() == 0
            && constr.getResultDomain().equals(domain);
    }

    /**
     * Decides if a term only contains predefined function symbols and variables
     */
    public static boolean onlyPredefined(final ITerm<?> t) {
        final Set<IFunctionSymbol<?>> leftFs = t.getFunctionSymbols();
        for (final IFunctionSymbol<?> fs : leftFs) {
            if (fs.getSemantics() == null) {
                return false;
            }
        }
        return true;
    }

    /**
     * Decides if a term only contains predefined arithmetic function symbols
     * and variables
     */
    public static boolean onlyPredefinedArithmetic(final ITerm<?> t,
        final IDPPredefinedMap predefinedMap) {
        final Set<IFunctionSymbol<?>> leftFs = t.getFunctionSymbols();
        for (final IFunctionSymbol<?> fs : leftFs) {
            final PredefinedSemantics<?> semantics = fs.getSemantics();
            if (semantics != null) {
                if (semantics.isConstructor()) {
                    if (((PredefinedConstructor<?>) semantics).getResultDomain().isIntegerDomain()) {
                        return false;
                    }
                } else {
                    if (((PredefinedFunction<?, ?>) semantics).isArithmetic()) {
                        return false;
                    }
                }
            } else {
                return false;
            }
        }
        return true;
    }

    public static boolean hasPredefinedFunction(final ITerm<?> t) {
        for (final IFunctionSymbol<?> fs : t.getFunctionSymbols()) {
            if (PredefinedUtil.getPredefinedFunction(fs) != null) {
                return true;
            }
        }

        return false;
    }

    public static boolean isFunction(final IFunctionSymbol<?> fs, final Func func) {
        return fs.getSemantics() != null
            && !fs.getSemantics().isConstructor()
            && ((PredefinedFunction<?, ?>) fs.getSemantics()).getFunc() == func;
    }

    public static boolean isPredefined(final IFunctionSymbol<?> fs) {
        return fs.getSemantics() != null;
    }

    public static boolean isArithemeticFunction(final IFunctionSymbol<?> fs) {
        final PredefinedSemantics<?> semantics = fs.getSemantics();
        return semantics != null && !semantics.isConstructor()
            && ((PredefinedFunction<?, ?>) semantics).isArithmetic();
    }

    public static boolean isPolynomialTerm(final ITerm<?> term) {
        for (final IFunctionSymbol<?> fs : term.getFunctionSymbols()) {
            if (!fs.isPredefined()) {
                return false;
            }
            final PredefinedSemantics<?> semantics = fs.getSemantics();
            if (semantics.isConstructor()) {
                final PredefinedConstructor<?> constr = (PredefinedConstructor<?>) semantics;
                if (!constr.getResultDomain().isIntegerDomain()) {
                    return false;
                }
            } else {
                final PredefinedFunction<?, ?> function = (PredefinedFunction<?, ?>) semantics;

                for (final Domain dom : function.getDomains()) {
                    if (!dom.isIntegerDomain()) {
                        return false;
                    }
                }

                if (!function.getResultDomain().isIntegerDomain()) {
                    return false;
                }


                final Func func = function.getFunc();
                if (func != Func.Add && func != Func.Sub && func != Func.UnaryMinus && func != Func.Mul) {
                    return false;
                }
            }
        }

        for (final IVariable<?> var : term.getVariables()) {
            if (var.getDomain() == null || !var.getDomain().isIntegerDomain()) {
                return false;
            }
        }

        return true;
    }

}
