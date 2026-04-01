package aprove.verification.oldframework.Bytecode.Processors.PathLength;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv2.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.BoundedInts.*;

/**
 * A collection of helper functions.
 * @author Matthias Hoelzel
 */
public class PathLengthUtil {
    /**
     * The predefined map.
     */
    private final IDPPredefinedMap predefinedMap;

    /**
     * The function symbol that represents java objects.
     */
    final FunctionSymbol JAVA_LANG_OBJECT_SYMBOL = FunctionSymbol.create(
        InstanceTransformer.JAVA_LANG_OBJECT_NAME.getName(),
        InstanceTransformer.JAVA_LANG_OBJECT_NAME.getArity());

    /** The name of jlo-Symbols */
    final String JAVA_LANG_OBJECT_NAME =
        InstanceTransformer.JAVA_LANG_OBJECT_NAME.getName();

    /**
     * The end of class symbol.
     */
    final FunctionSymbol END_OF_CLASS = FunctionSymbol.create(
        InstanceTransformer.END_OF_CLASS_NAME.getName(),
        InstanceTransformer.END_OF_CLASS_NAME.getArity());

    /**
     * The function symbol that represents a null-pointer.
     */
    final FunctionSymbol NULL = FunctionSymbol.create(
        InstanceTransformer.NULL_NAME.getName(),
        InstanceTransformer.NULL_NAME.getArity());

    /**
     * The symbol for arrays.
     */
    final FunctionSymbol ARRAY_CONSTR = FunctionSymbol.create(
        ArrayTransformer.ARRAY_CONSTR.getName(),
        ArrayTransformer.ARRAY_CONSTR.getArity());

    /**
     * Type term representing a object.
     */
    final TRSFunctionApplication JLO_TYPE =
        TRSFunctionApplication.createFunctionApplication(FunctionSymbol.create(
            "jlO", 0));

    /**
     * Type term representing predefined elements: numbers or result of
     * arithmetical operations.
     */
    final TRSFunctionApplication PREDEFINED_TYPE =
        TRSFunctionApplication.createFunctionApplication(FunctionSymbol.create(
            "predef", 0));

    /**
     * The type of variables might be unknown.
     */
    final TRSFunctionApplication UNKNOWN_TYPE =
        TRSFunctionApplication.createFunctionApplication(FunctionSymbol.create(
            "unknown", 0));

    /**
     * Constructor.
     * @param predefMap a predefined map
     */
    public PathLengthUtil(final IDPPredefinedMap predefMap) {
        this.predefinedMap = predefMap;
    }

    /**
     * Calculates the type.
     * @param t a term
     * @return type term
     */
    public TRSTerm getType(final TRSTerm t) {
        if (t.isVariable()) {
            return t;
        }
        assert (t instanceof TRSFunctionApplication);
        final TRSFunctionApplication func = (TRSFunctionApplication) t;
        final FunctionSymbol sym = func.getRootSymbol();
        if (sym.equals(this.JAVA_LANG_OBJECT_SYMBOL) || sym.equals(this.NULL)
            || (sym.getName().contains(this.JAVA_LANG_OBJECT_NAME) && sym.getArity() == 1))
        {
            return this.JLO_TYPE;
        } else if (this.predefinedMap.isPredefined(sym)
            || BoundedSymbolFactory.isCastSymbol(sym)) {
            return this.PREDEFINED_TYPE;
        } else {
            return this.UNKNOWN_TYPE;
        }
    }

    /**
     * Build the term s + t.
     * @param s first term
     * @param t second term
     * @return another term
     */
    public TRSTerm buildAddition(final TRSTerm s, final TRSTerm t) {
        final ArrayList<TRSTerm> arguments = new ArrayList<TRSTerm>(2);
        arguments.add(s);
        arguments.add(t);
        final FunctionSymbol sym =
            this.predefinedMap.getSym(Func.Add, DomainFactory.INTEGERS);
        return TRSTerm.createFunctionApplication(sym, arguments);
    }

    /**
     * Returns true, iff the given symbol is predefined.
     * @param sym function symbol
     * @return boolean
     */
    public boolean isPredefined(final FunctionSymbol sym) {
        return this.predefinedMap.isPredefined(sym)
            || BoundedSymbolFactory.isCastSymbol(sym);
    }

    /**
     * Call predefined maps getIntSym(..) with correct arguments.
     * @param i BigInteger
     * @return symbol representing i
     */
    public FunctionSymbol getIntSym(final BigInteger i) {
        return this.predefinedMap.getIntSym(BigIntImmutable.create(i),
            DomainFactory.INTEGERS);
    }

    public TRSFunctionApplication getIntFunc(final BigInteger i) {
        return TRSTerm.createFunctionApplication(this.getIntSym(i));
    }

    public TRSTerm buildGreaterOrEqual(TRSTerm a, TRSTerm b) {
        final FunctionSymbol geSym = this.getPredefinedMap().getSym(Func.Ge, DomainFactory.INTEGERS);
        return TRSTerm.createFunctionApplication(geSym, a, b);
    }

    /**
     * Returns the wrapped predefined map.
     * @return IDPPredefinedMap
     */
    public IDPPredefinedMap getPredefinedMap() {
        return this.predefinedMap;
    }

    /**
     * Rewrites a polynomial to a term. Here I assume the polynomial to be
     * concrete!
     * @param vp a VarPolynomial
     * @return a term
     */
    public TRSTerm rewriteVarPolynomialToTerm(final VarPolynomial vp) {
        TRSTerm result = null;
        for (final Entry<IndefinitePart, SimplePolynomial> entry : vp.getVarMonomials().entrySet()) {
            final IndefinitePart indefPart = entry.getKey();
            final SimplePolynomial simplePart = entry.getValue();

            assert simplePart.isConstant() : "There must not be any indefinite coefficients!";

            final BigInteger bi = simplePart.getNumericalAddend();
            TRSTerm current = null;
            if (bi.equals(BigInteger.ZERO)) {
                continue;
            } else if (!bi.equals(BigInteger.ONE)) {
                current =
                    this.predefinedMap.getIntTerm(BigIntImmutable.create(bi),
                        DomainFactory.INTEGERS);
            }

            for (final Entry<String, Integer> expoEntry : indefPart.getExponents().entrySet()) {
                final String var = expoEntry.getKey();
                Integer exp = expoEntry.getValue();
                final TRSVariable varVar = TRSTerm.createVariable(var);
                if (current == null) {
                    current = varVar;
                }
                while (exp > 1) {
                    exp--;
                    current =
                        TRSTerm.createFunctionApplication(
                            this.predefinedMap.getSym(Func.Mul,
                                DomainFactory.INTEGERS), current, varVar);
                }
            }
            if (current == null) {
                current =
                    this.predefinedMap.getIntTerm(
                        BigIntImmutable.create(BigInteger.ONE),
                        DomainFactory.INTEGERS);
            }

            if (result == null) {
                result = current;
            } else {
                result = this.buildAddition(result, current);
            }
        }
        if (result == null) {
            result =
                this.predefinedMap.getIntTerm(
                    BigIntImmutable.create(BigInteger.ZERO),
                    DomainFactory.INTEGERS);
        }
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("pathlength");
            l.logln("\nTurned " + vp + " into " + result);
        }
        return result;
    }
}
