package aprove.verification.oldframework.Bytecode.Processors.ToMCNP;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;


/**
 *
 * A collection of commonly used methods.
 *
 * @author Matthias Hoelzel
 *
 */
public final class IDPToMCSUtility {
    /**
     * Needed for generating fresh and tasty names.
     */
    private static int counter;

    /**
     * Private constructor.
     */
    private IDPToMCSUtility() {
    }

    /**
     * Creates the term representing t1 + t2.
     *
     * @param t1 a term
     * @param t2 another term
     * @return a term
     */
    public static TRSTerm createAdditionTerm(final TRSTerm t1, final TRSTerm t2) {
        final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
        args.add(t1);
        args.add(t2);
        return TRSTerm.createFunctionApplication(IDPPredefinedMap.DEFAULT_MAP.getSym(
                Func.Add, DomainFactory.INTEGERS), args);
    }

    /**
     * Creates a term representing [val].
     *
     * @param val an int
     * @return a term
     */
    public static TRSTerm createIntegerTerm(final int val) {
        return IDPPredefinedMap.DEFAULT_MAP.getIntTerm(BigIntImmutable.create(BigInteger
                .valueOf(val)), DomainFactory.INTEGERS);
    }

    /**
     * Generate a fresh name.
     *
     * @return a String
     */
    public static String getFreshName() {
        // Fresh and tasty!
        IDPToMCSUtility.counter++;
        return "var" + IDPToMCSUtility.counter;
    }
}
