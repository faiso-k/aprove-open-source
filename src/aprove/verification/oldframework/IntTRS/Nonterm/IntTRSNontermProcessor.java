package aprove.verification.oldframework.IntTRS.Nonterm;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Class to conviently provide methods needed for nonterm proofs.
 *
 * @author Marc Brockschmidt
 */
public abstract class IntTRSNontermProcessor extends Processor.ProcessorSkeleton {
    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSwTProblem && ((IRSwTProblem) obl).isIRS() && Options.certifier.isNone();
    }

    /**
     * Given
     *  f(x1, ..., xn) -> g(t1, ..., tn)
     * gives a SMT formula
     *     varPrefix'_1 = t1[x1/varPrefix_1, ..., xn/varPrefix_n]
     *  && ...
     *  && varPrefix'_n = t1[x1/varPrefix_1, ..., xn/varPrefix_n]
     * @param inRule some rule
     * @param lhsPrefix the prefix used for the (bound) variables on the left and fresh variables
     * @param rhsPrefix the prefix used for the new variables
     * @param factory some formula factory
     * @return a pair of formulae, the first encoding the variable updates, the second the conditions
     */
    public static Pair<Formula<SMTLIBTheoryAtom>, Formula<SMTLIBTheoryAtom>> turnRuleIntoSMTFormulae(
        final IGeneralizedRule inRule,
        final String lhsPrefix,
        final String rhsPrefix,
        final FormulaFactory<SMTLIBTheoryAtom> factory
    ) {
        final IGeneralizedRule rule = inRule.getWithRenumberedVariables(lhsPrefix);
        //Get the primed variables (from the lhs, which only has vars, and has the same arity as the rhs by contract):
        final TRSFunctionApplication primedLhs = (TRSFunctionApplication) inRule.getLeft().renumberVariables(rhsPrefix);
        final TRSFunctionApplication rhs = (TRSFunctionApplication) rule.getRight();
        final ImmutableList<TRSTerm> args = rhs.getArguments();
        final FreshNameGenerator ng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        // The variable updates:
        final List<SMTLIBTheoryAtom> updateFormula = new LinkedList<>();
        for (int i = 0; i < args.size(); i++) {
            final TRSVariable updateVar = (TRSVariable) primedLhs.getArgument(i);
            final TRSTerm updateTerm = args.get(i);
            updateFormula.add(
                SMTLIBIntEquals.create(
                    SMTLIBIntVariable.create(updateVar.getName()),
                    ToolBox.intTermToPolynomial(updateTerm, ng).toSMTLIB()
                )
            );
        }
        final Formula<SMTLIBTheoryAtom> updates = factory.buildAnd(factory.buildTheoryAtoms(updateFormula));
        // The condition:
        final TRSTerm cond = rule.getCondTerm();
        final Formula<SMTLIBTheoryAtom> conditions;
        if (cond != null) {
            conditions = ToolBox.boolTermToSMT_QF_IA(cond, factory, ng);
        } else {
            conditions = factory.buildConstant(true);
        }
        return new Pair<>(updates, conditions);
    }

    /**
     * Chooses a map m from existing function symbols to an integer. Then turns rules
     * like
     *  f(x1, ..., xn) -> g(t1, ..., tm) | c
     * into a new rule
     *  f(pc, x1, ..., xn, y1 ..., yk) -> g(map(r), t1, ..., tm, z1, ..., zl) | pc = map(f) && c
     * such that n + k = argNum and m + l = argNum holds. We will then later just ignore the enclosing symbols.
     * @param rules some rules
     * @return the modified rules
     */
    public static Set<IGeneralizedRule> moveFsIntoArgsAndNormalize(final Set<IGeneralizedRule> rules) {
        final Map<FunctionSymbol, Integer> pcMap = new LinkedHashMap<>();

        int pc = 0;
        int maxVarNum = 0;
        for (final IGeneralizedRule rule : rules) {
            final FunctionSymbol lhsSym = rule.getRootSymbol();
            maxVarNum = Math.max(maxVarNum, lhsSym.getArity());
            if (!pcMap.containsKey(lhsSym)) {
                pcMap.put(lhsSym, Integer.valueOf(++pc));
            }

            final TRSTerm rhs = rule.getRight();
            if (!rhs.isVariable()) {
                final FunctionSymbol rhsSym = ((TRSFunctionApplication) rhs).getRootSymbol();
                if (!pcMap.containsKey(rhsSym)) {
                    pcMap.put(rhsSym, Integer.valueOf(++pc));
                }
            }

        }

        final Set<IGeneralizedRule> newRules = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : rules) {
            newRules.add(IntTRSNontermProcessor.moveFsIntoArgs(rule, maxVarNum, pcMap));
        }

        return newRules;
    }

    /**
     * @param rule Some rule f(x1, ..., xn) -> g(t1, ..., tm) | c
     * @param argNum number of arguments every term should have after we are done (plus one for the pc). Should be at
     *  least the max of the arity of all occurring defined symbols
     * @param pcMap map from function symbols to integer
     * @return a new rule f(pc, x1, ..., xn, y1 ..., yk) -> g(map(r), t1, ..., tm, z1, ..., zl) | pc = map(f) && c
     *  such that n + k = argNum and m + l = argNum holds
     */
    private static IGeneralizedRule moveFsIntoArgs(
        final IGeneralizedRule rule,
        final int argNum,
        final Map<FunctionSymbol, Integer> pcMap)
    {
        final TRSFunctionApplication lhs = rule.getLeft();
        final TRSTerm rhs = rule.getRight();
        final TRSTerm cond = rule.getCondTerm();

        final FreshNameGenerator fne = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        fne.lockHasNames(lhs.getVariables());
        final TRSVariable freshPCVar = TRSTerm.createVariable(fne.getFreshName("pc", false));

        final FunctionSymbol lhsFs = lhs.getRootSymbol();
        assert (lhsFs.getArity() <= argNum) : "FS has more arguments than allowed";
        final ArrayList<TRSTerm> newLhsArgs = new ArrayList<>(argNum + 1);
        newLhsArgs.add(freshPCVar);
        newLhsArgs.addAll(lhs.getArguments());
        //Intentional off-by-one (we want argNum+1 arguments!):
        for (int i = newLhsArgs.size(); i <= argNum; i++) {
            newLhsArgs.add(TRSTerm.createVariable(fne.getFreshName("y", false)));
        }
        final TRSFunctionApplication newLhs =
            TRSTerm.createFunctionApplication(FunctionSymbol.create("f", argNum + 1), newLhsArgs);

        assert (!rhs.isVariable()) : "intTRS with rhs just a variable. Help!";

        final TRSFunctionApplication rhsFA = (TRSFunctionApplication) rhs;
        final FunctionSymbol rhsFs = rhsFA.getRootSymbol();
        assert (rhsFs.getArity() <= argNum) : "FS has more arguments than allowed";
        final ArrayList<TRSTerm> newRhsArgs = new ArrayList<>(argNum + 1);
        newRhsArgs.add(TRSTerm.createFunctionApplication(FunctionSymbol.create(pcMap.get(rhsFs).toString(), 0)));
        newRhsArgs.addAll(rhsFA.getArguments());
        //Intentional off-by-one (we want argNum+1 arguments!):
        for (int i = newRhsArgs.size(); i <= argNum; i++) {
            newRhsArgs.add(TRSTerm.createVariable(fne.getFreshName("z", false)));
        }
        final TRSFunctionApplication newRhs =
            TRSTerm.createFunctionApplication(FunctionSymbol.create("f", argNum + 1), newRhsArgs);

        final TRSTerm pcEq =
            TRSTerm.createFunctionApplication(
                FunctionSymbol.create("=", 2),
                freshPCVar,
                TRSTerm.createFunctionApplication(FunctionSymbol.create(pcMap.get(lhsFs).toString(), 0)));

        final TRSTerm newCond = IDPv2ToIDPv1Utilities.getConjunction(pcEq, cond);

        return IGeneralizedRule.create(newLhs, newRhs, newCond);
    }
}
