/**
 *
 */
package aprove.verification.oldframework.IRSwT.Filters;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Removes non-predefined symbols.
 * @author Matthias Hoelzel
 *
 */
public class RemoveTermFilter extends SortFilter {
    /** Generates fresh names. */
    private final FreshNameGenerator fng;

    /**
     * Constructor!
     * @param inputRules set of rules
     * @param dictionary sort dictionary
     * @param gen some fresh name generator
     */
    public RemoveTermFilter(
        final Set<IGeneralizedRule> inputRules,
        final SortDictionary dictionary,
        final FreshNameGenerator gen)
    {
        super(inputRules, dictionary);
        this.fng = gen;
    }

    /**
     * Given a term, this will filtered away terms and mixed-arguments.
     * @param t a term
     * @return a filtered term
     */
    @Override
    public TRSTerm filterTerm(final TRSTerm t) {
        if (t instanceof TRSFunctionApplication) {
            // We do not need to keep position here
            final TRSTerm noAlwaysTerms = this.removeSort(t, Sort.FUNAPP);
            assert noAlwaysTerms instanceof TRSFunctionApplication : "Should be function application!";

            final TRSFunctionApplication f = (TRSFunctionApplication) noAlwaysTerms;
            final FunctionSymbol sym = f.getRootSymbol();
            final ArrayList<TRSTerm> newArgs = new ArrayList<>(sym.getArity());
            for (final TRSTerm arg : f.getArguments()) {
                newArgs.add(this.filterArgument(arg));
            }
            return TRSTerm.createFunctionApplication(sym, newArgs);
        } else {
            return t;
        }
    }

    /**
     * Replace non-predefined symbols by 0.
     * @param t some term
     * @return some purged term
     */
    public TRSTerm filterArgument(final TRSTerm t) {
        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication f = (TRSFunctionApplication) t;
            final FunctionSymbol sym = f.getRootSymbol();

            if (IDPPredefinedMap.DEFAULT_MAP.isPredefined(sym)) {
                return t;
            } else {
                return ToolBox.buildInt(BigInteger.ZERO);
            }
        } else {
            return t;
        }
    }

    @Override
    protected IGeneralizedRule processRule(final IGeneralizedRule inputRule) {
        final TRSFunctionApplication left = inputRule.getLeft();
        final TRSFunctionApplication right = (TRSFunctionApplication) inputRule.getRight();
        final FunctionSymbol leftSym = left.getRootSymbol();
        final FunctionSymbol rightSym = right.getRootSymbol();
        final ArrayList<TRSTerm> newLeftArgs = new ArrayList<>(leftSym.getArity());
        final ArrayList<TRSTerm> newRightArgs = new ArrayList<>(rightSym.getArity());
        TRSTerm conditionAddition = null;
        for (final TRSTerm arg : left.getArguments()) {
            if (!arg.isVariable()) {
                final TRSVariable v = TRSTerm.createVariable(this.fng.getFreshName("c", false));
                newLeftArgs.add(v);
                if (conditionAddition == null) {
                    conditionAddition = ToolBox.buildEq(v, arg);
                } else {
                    conditionAddition = ToolBox.buildAnd(ToolBox.buildEq(v, arg), conditionAddition);
                }
            } else {
                assert arg.isVariable() : "Non-constant function application?!?";
                newLeftArgs.add(arg);
            }
        }
        final TRSFunctionApplication newLeft = TRSTerm.createFunctionApplication(leftSym, newLeftArgs);

        for (final TRSTerm arg : right.getArguments()) {
            if (!arg.isVariable()) {
                final TRSVariable v = TRSTerm.createVariable(this.fng.getFreshName("c", false));
                newRightArgs.add(v);
                if (conditionAddition == null) {
                    conditionAddition = ToolBox.buildEq(v, arg);
                } else {
                    conditionAddition = ToolBox.buildAnd(ToolBox.buildEq(v, arg), conditionAddition);
                }
            } else {
                assert arg.isVariable() : "Non-constant function application?!?";
                newRightArgs.add(arg);
            }
        }
        final TRSFunctionApplication newRight = TRSTerm.createFunctionApplication(rightSym, newRightArgs);

        final TRSTerm oldCondition = inputRule.getCondTerm();
        final TRSTerm newCondition;
        if (conditionAddition == null) {
            newCondition = oldCondition;
        } else {
            newCondition =
                ToolBox.buildAnd(conditionAddition, oldCondition == null ? ToolBox.buildTrue() : oldCondition);
        }

        final IGeneralizedRule resultRule = IGeneralizedRule.create(newLeft, newRight, newCondition);
        return resultRule;
    }

    @Override
    public String export(final Export_Util eu) {
        return eu.tttext("Replaced non-predefined constructor symbols by 0.");
    }
}
