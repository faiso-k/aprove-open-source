package aprove.verification.oldframework.IntTRS.BoundedInts;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import immutables.*;

/**
 * Remove some unneeded cast-symbols
 * @author Matthias Hoelzel
 */
public class CastSymbolRemover {
    /** Current form of the input rule. */
    private IGeneralizedRule current;

    /** Output rule! */
    private IGeneralizedRule outputRule;

    /** Range information */
    private final Map<TRSVariable, IntegerType> ranges;

    /**
     * Constructor!
     * @param input some IGeneralizedRule.
     */
    public CastSymbolRemover(final IGeneralizedRule input, final Map<TRSVariable, IntegerType> rangeInfo) {
        this.current = input;
        this.ranges = (rangeInfo == null) ? new LinkedHashMap<TRSVariable, IntegerType>(0) : rangeInfo;
        this.outputRule = null;
    }

    /**
     * Returns the output rule!
     * @return IGeneralizedRule
     */
    public IGeneralizedRule getOutput() {
        if (this.outputRule == null) {
            this.generateOutputRule();
        }
        return this.outputRule;
    }

    /**
     * Generates the output rule!
     */
    private void generateOutputRule() {
        // Remove unneeded casts
        this.removeUnneededCasts();
        this.outputRule = this.current;
    }

    /**
     * Removes unneeded casts. For example we can avoid some nested casts and
     * casts of constants and single variables are unnecessary.
     */
    private void removeUnneededCasts() {
        // 1. No casts of variables & constants:
        this.removeTrivialCasts();

        // 2. Remove nested casts
        this.removeNestedCasts();
    }

    /**
     * Simplifies terms like cast_32_signed(5) to 5 and terms like
     * cast_32_signed(x) to x.
     */
    private void removeTrivialCasts() {
        final TRSFunctionApplication left = this.current.getLeft();
        final TRSFunctionApplication oldRight = (TRSFunctionApplication) this.current.getRight();
        TRSTerm oldCondition = this.current.getCondTerm();
        if (oldCondition == null) {
            oldCondition = ToolBox.buildTrue();
        }

        final TRSFunctionApplication newRightSide = (TRSFunctionApplication) this.removeTrivialCasts(oldRight);
        final TRSTerm newCondition = this.removeTrivialCasts(oldCondition);

        this.current = IGeneralizedRule.create(left, newRightSide, newCondition);
    }

    /**
     * Simplifies terms like cast_32_signed(5) to 5 and terms like
     * cast_32_signed(x) to x.
     * @param t a term
     * @return another term
     */
    private TRSTerm removeTrivialCasts(final TRSTerm t) {
        if (t.isVariable()) {
            return t;
        } else {
            final TRSFunctionApplication func = (TRSFunctionApplication) t;
            final FunctionSymbol sym = func.getRootSymbol();
            if (BoundedSymbolFactory.isCastSymbol(sym)) {
                assert sym.getArity() == 1;
                final TRSTerm arg = func.getArgument(0);
                if (arg.isVariable()) {
                    if (this.ranges.containsKey(arg)) {
                        final IntegerType db = this.ranges.get(arg);
                        if (db != null
                            && BoundedSymbolFactory.getMinValue(sym).compareTo(db.getLower().getConstant()) >= 0
                            && BoundedSymbolFactory.getMaxValue(sym).compareTo(db.getUpper().getConstant()) <= 0) {
                            return arg;
                        }
                    }
                    return func;
                } else if (arg.isConstant()) {
                    final BigInteger bi =
                        IDPPredefinedMap.DEFAULT_MAP.getInt(((TRSFunctionApplication) arg).getRootSymbol(),
                            DomainFactory.INTEGERS);
                    assert bi != null : "Constant is not a number: " + arg;
                    final BigInteger normalized = BoundedSymbolFactory.getNormalizedValue(sym, bi);
                    return IDPPredefinedMap.DEFAULT_MAP.getIntTerm(BigIntImmutable.create(normalized),
                        DomainFactory.INTEGERS);
                } else {
                    return TRSTerm.createFunctionApplication(sym, this.removeTrivialCasts(arg));
                }
            } else {
                // Recursive descent:
                func.getArguments();
                final ImmutableList<TRSTerm> args = func.getArguments();
                final ArrayList<TRSTerm> newArguments = new ArrayList<>(args.size());
                for (final TRSTerm arg : args) {
                    newArguments.add(this.removeTrivialCasts(arg));
                }
                return TRSTerm.createFunctionApplication(sym, newArguments);
            }
        }
    }

    /**
     * Simplifies
     * cast_32_signed(cast_32_signed(x)+cast_32_signed(y)*cast_32_signed(z)) to
     * cast_32_signed(x+y*z). However, a term like
     * cast_32_signed(cast_16_signed(x) + cast_16_signed(y)) cannot be
     * simplified to cast_32_signed(x + y), so nested cast-symbols with
     * different ranges have to remain.
     */
    private void removeNestedCasts() {
        final TRSFunctionApplication left = this.current.getLeft();
        final TRSTerm right = BoundedSymbolFactory.removeUnnecessaryCastSymbols(this.current.getRight());
        final TRSTerm cond = BoundedSymbolFactory.removeUnnecessaryCastSymbols(this.current.getCondTerm());

        this.current = IGeneralizedRule.create(left, right, cond);
    }
}
