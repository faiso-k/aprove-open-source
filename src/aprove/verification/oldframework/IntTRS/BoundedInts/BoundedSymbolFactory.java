package aprove.verification.oldframework.IntTRS.BoundedInts;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import immutables.*;

/**
 * Produces cast-Symbols cast_32_signed(..). This class also contains some
 * auxiliary function; for instance it can simplify given terms by removing some
 * unnecessary nested cast-symbols.
 * @author Matthias Hoelzel
 */
public final class BoundedSymbolFactory {
    /**
     * Create a cast for (un)signed-bit arithmetic.
     * @param numBits number of bits
     * @param signed signed or not
     * @return cast-symbol of arity 1
     */
    public static FunctionSymbol createCastSymbol(final int numBits, final boolean signed) {
        assert numBits > 0 : "Invalid number of bits : " + numBits;
        final String symbolName = "cast_" + numBits + "_" + (signed ? "signed" : "unsigned");
        return FunctionSymbol.create(symbolName, 1);
    }

    /**
     * Returns true, iff sym is a cast-symbol.
     * @param sym function symbol
     * @return boolean
     */
    public static boolean isCastSymbol(final FunctionSymbol sym) {
        assert sym != null : "sym is null!";
        final String name = sym.getName();
        return sym.getArity() == 1 && name.matches("cast_[1-9][0-9]*+_(un)?+signed");
    }

    /**
     * Returns true, if a given term contains a cast symbol.
     * @param t term
     * @return boolean
     */
    public static boolean containsCastSymbol(final TRSTerm t) {
        assert t != null : "Term is null!";
        if (t.isVariable()) {
            return false;
        } else {
            assert t instanceof TRSFunctionApplication : "Non-variable should be function application!";
            final TRSFunctionApplication func = (TRSFunctionApplication) t;
            if (BoundedSymbolFactory.isCastSymbol(func.getRootSymbol())) {
                return true;
            } else {
                for (final TRSTerm arg : func.getArguments()) {
                    if (BoundedSymbolFactory.containsCastSymbol(arg)) {
                        return true;
                    }
                }
                return false;
            }
        }
    }

    /**
     * Extracts the number of bits from the given cast symbol.
     * @param sym function symbol
     * @return int
     */
    public static int getNumberOfBits(final FunctionSymbol sym) {
        assert BoundedSymbolFactory.isCastSymbol(sym) : "Not a cast symbol: " + sym.toString();
        final String numBitsString = sym.getName().split("_")[1];
        return Integer.parseInt(numBitsString);
    }

    /**
     * Casting to signed arithmetic?
     * @param sym function symbol
     * @return boolean
     */
    public static boolean isSigned(final FunctionSymbol sym) {
        assert BoundedSymbolFactory.isCastSymbol(sym) : "Not a cast symbol: " + sym.toString();
        final String name = sym.getName();
        return name.matches("cast_[1-9][0-9]*+_signed");
    }

    /**
     * Calculates the number of possible values.
     * @param sym function symbol
     * @return BigInteger
     */
    public static BigInteger getRange(final FunctionSymbol sym) {
        final int bits = BoundedSymbolFactory.getNumberOfBits(sym);
        return BigInteger.valueOf(2).pow(bits);
    }

    /**
     * Return the maximal value this cast-symbol could produce.
     * @param sym function symbol
     * @return BitInteger
     */
    public static BigInteger getMaxValue(final FunctionSymbol sym) {
        final boolean isSigned = BoundedSymbolFactory.isSigned(sym);
        final int bits = BoundedSymbolFactory.getNumberOfBits(sym);
        if (isSigned) {
            return BigInteger.valueOf(2).pow(bits - 1).subtract(BigInteger.ONE);
        } else {
            return BigInteger.valueOf(2).pow(bits).subtract(BigInteger.ONE);
        }
    }

    /**
     * Return the minimal value this cast-symbol could produce.
     * @param sym function symbol
     * @return BitInteger
     */
    public static BigInteger getMinValue(final FunctionSymbol sym) {
        final boolean isSigned = BoundedSymbolFactory.isSigned(sym);
        final int bits = BoundedSymbolFactory.getNumberOfBits(sym);
        if (isSigned) {
            return BigInteger.valueOf(2).pow(bits - 1).negate();
        } else {
            return BigInteger.ZERO;
        }
    }

    /**
     * Normalizes w.r.t. given bit-vector arithmetic.
     * @param castSymbol a cast symbol
     * @param value some BigInteger
     * @return another BigInteger
     */
    public static BigInteger getNormalizedValue(final FunctionSymbol castSymbol, final BigInteger value) {
        final BigInteger range = BoundedSymbolFactory.getRange(castSymbol);
        if (!BoundedSymbolFactory.isSigned(castSymbol)) {
            final BigInteger almostResult = value.mod(range);
            if (almostResult.compareTo(BigInteger.ZERO) >= 0) {
                return almostResult;
            } else {
                return almostResult.add(range);
            }
        } else {
            final BigInteger almostResult = value.mod(range);
            if (almostResult.compareTo(BigInteger.ZERO) < 0) {
                return almostResult.add(range);
            }
            assert almostResult.compareTo(BigInteger.ZERO) >= 0 && almostResult.compareTo(range) < 0 : "Invalid remainder!!";
            if (almostResult.compareTo(range.divide(BigInteger.valueOf(2))) >= 0) {
                return almostResult.subtract(range);
            } else {
                return almostResult;
            }
        }
    }

    /**
     * Simplifies terms like
     * cast_32_signed(cast_32_signed(x)*cast_32_unsigned(y) + cast_32_signed(z))
     * to cast_32_signed(x*y + z).
     * @param t term to simplify
     * @return simplified term
     */
    public static TRSTerm removeUnnecessaryCastSymbols(final TRSTerm t) {
        assert t != null : "Term is null!";
        return BoundedSymbolFactory.removingUnnecessaryCastSymbols(t, null);
    }

    /**
     * Simplifies terms like
     * cast_32_signed(cast_32_signed(x)*cast_32_unsigned(y) + cast_32_signed(z))
     * to cast_32_signed(x*y + z).
     * @param t term to simplify
     * @param currentRange the current we visit or null
     * @return simplified termf
     */
    private static TRSTerm removingUnnecessaryCastSymbols(final TRSTerm t, final BigInteger currentRange) {
        if (t.isVariable()) {
            return t;
        } else {
            final TRSFunctionApplication func = (TRSFunctionApplication) t;
            final FunctionSymbol sym = func.getRootSymbol();
            if (BoundedSymbolFactory.isCastSymbol(sym)) {
                final BigInteger otherRange = BoundedSymbolFactory.getRange(sym);
                if (currentRange != null && currentRange.equals(otherRange)) {
                    return BoundedSymbolFactory.removingUnnecessaryCastSymbols(func.getArgument(0), currentRange);
                } else {
                    return TRSTerm.createFunctionApplication(
                        sym,
                        BoundedSymbolFactory.removingUnnecessaryCastSymbols(func.getArgument(0), otherRange));
                }
            } else {
                final ImmutableList<TRSTerm> args = func.getArguments();
                final List<TRSTerm> newArgs = new ArrayList<>(args.size());
                for (final TRSTerm arg : args) {
                    newArgs.add(BoundedSymbolFactory.removingUnnecessaryCastSymbols(arg, currentRange));
                }
                return TRSTerm.createFunctionApplication(sym, newArgs);
            }
        }
    }

    /**
     * Returns the corresponding domain of a cast-symbol. Example:
     * cast_32_signed -> 32-Bit-Signed.
     * @param sym some cast-symbol
     * @return BoundedDomain
     */
    public static IntegerType getCorrespondingDomain(final FunctionSymbol sym) {
        final int bits = BoundedSymbolFactory.getNumberOfBits(sym);
        final boolean signed = BoundedSymbolFactory.isSigned(sym);
        return new IntegerType(bits, signed);
    }
}
