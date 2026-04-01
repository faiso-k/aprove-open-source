package aprove.verification.dpframework.CLSProblem.Utility;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Helper class for function symbols with predefined semantics for CLS.
 *
 * <p>CLS have some function symbols with predefined semantics. This class
 * creates instances of these symbols as well as a facility to
 * generate {@link FunctionSymbol}s for integers.</p>
 *
 * <p>To add a new function symbol, add it to the enum {@link PredefinedFunctions}</p>
 *
 * <p>Integer constants are a special case, as there are so many of them. For
 * this reason, they do not appear in {@link PredefinedFunctions}.</p>
 *
 * @author noschinski
 * @version $Id$
*/
public class PredefinedHelper {
    /**
     * Symbols which may only occur in the condition of a CLS rule
     */
    public static final Set<FunctionSymbol> CONDITION_SYMBOLS =
        new LinkedHashSet<FunctionSymbol>();
    public static final Set<FunctionSymbol> RELATION_SYMBOLS =
        new LinkedHashSet<FunctionSymbol>();

    static {
        PredefinedHelper.CONDITION_SYMBOLS.add(PredefinedFunctions.And.getSym());
        PredefinedHelper.CONDITION_SYMBOLS.add(PredefinedFunctions.Or.getSym());
        PredefinedHelper.CONDITION_SYMBOLS.add(PredefinedFunctions.Not.getSym());

        PredefinedHelper.RELATION_SYMBOLS.add(PredefinedFunctions.Clt.getSym());
        PredefinedHelper.RELATION_SYMBOLS.add(PredefinedFunctions.Cle.getSym());
        PredefinedHelper.RELATION_SYMBOLS.add(PredefinedFunctions.Ceq.getSym());
        PredefinedHelper.RELATION_SYMBOLS.add(PredefinedFunctions.Cge.getSym());
        PredefinedHelper.RELATION_SYMBOLS.add(PredefinedFunctions.Cgt.getSym());
    }

    /**
     * Set of predefined symbols
     */
    public final static ImmutableSet<FunctionSymbol> PREDEF_SYMS =
        ImmutableCreator.create(PredefinedFunctions.SYM_MAP.keySet());

    /**
     * Creates a Term representing the Integer <code>integer</code>.
     *
     * @throws NumberFormatException if <code>integer</code> is not a
     *      valid integer.
     */
    public static TRSFunctionApplication termInt(String integer) {
        return TRSTerm.createFunctionApplication(PredefinedHelper.symInt(integer), TRSTerm.EMPTY_ARGS);
    }

    /**
     * Creates an function symbol for an integer.
     * @throws NumberFormatException if <code>integer</code> is not a
     *      valid integer.
     */
    public static FunctionSymbol symInt(String integer) {
        if (PredefinedHelper.isInt(integer)) {
            return FunctionSymbol.create(integer, 0);
        } else {
            throw new NumberFormatException(integer);
        }
    }

    /**
     * Decides if a function symbol is a predefined one.
     */
    public static boolean isPredefined(FunctionSymbol fs) {
        return PredefinedHelper.PREDEF_SYMS.contains(fs) || PredefinedHelper.isInt(fs);
    }

    /**
     * Decides if a function symbol represents an integer.
     */
    public static boolean isInt(FunctionSymbol fs) {
        return fs.getArity() == 0 && PredefinedHelper.isInt(fs.getName());
    }

    /**
     * Decides if the function name represents an integer.
     */
    // FIXME: Integers ore only natural numbers?
    public static boolean isInt(String name) {
        try {
            new BigInteger(name);
            return true;
        } catch (NumberFormatException e) {
            return false;
        }
    }

    /**
     * Converts an integer function symbol to a {@link BigInteger}.
     *
     * <p>Semantics are only defined for function symbols where
     * <code>isInteger</code> returns true.</p>
     *
     * @throws NumberFormatException if <code>fs</code> is not an integer.
     */
    public static BigInteger toInteger(FunctionSymbol fs) {
        return new BigInteger(fs.getName());
    }

    public static NameProvider getNameProvider() {
        return new CLSPredefinedNameProvider();
    }

}
