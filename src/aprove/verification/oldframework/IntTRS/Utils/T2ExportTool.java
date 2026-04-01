package aprove.verification.oldframework.IntTRS.Utils;

import aprove.Globals;
import aprove.input.Generated.IntTRS.IntTRSLexer;
import aprove.input.Generated.IntTRS.IntTRSParser;
import aprove.exit.KillAproveException;
import aprove.input.Programs.t2.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

import org.antlr.runtime.ANTLRReaderStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.*;

/**
 * Convenience things to export stuff to T2.
 *
 * @author Marc Brockschmidt
 */
public abstract class T2ExportTool {
    public static void main(final String... args) {
        try {
            doMain(args);
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }

    private static void doMain(final String... args) throws KillAproveException {
        if (args.length > 1) {
            System.err.println("Usage: T2ExportTool INPUTFILE -- no extra arguments allowed.");
            throw new KillAproveException(1);
        }
        final File inFile = new File(args[0]);

        try {
            final FileReader reader = new FileReader(inFile);

            //Read the intTRS:
            final IntTRSLexer lex = new IntTRSLexer(new ANTLRReaderStream(reader));
            final CommonTokenStream tokens = new CommonTokenStream(lex);
            final IntTRSParser parser = new IntTRSParser(tokens);
            final IRSwTProblem irswt = parser.intTRS();

            //Transform it:
            final T2IntSys t2Sys = T2ExportTool.transformIntTRSToT2(new IRSProblem(irswt.getRules(), irswt.getStartTerm())).x;
            System.out.println(t2Sys.export(new PLAIN_Util()));
        } catch (final FileNotFoundException e) {
            System.err.println("Could not open file " + args[0]);
            throw new KillAproveException(1);
        } catch (final RecognitionException re) {
            System.err.println("Could not parse file " + args[0] + ":\n" + re);
            throw new KillAproveException(1);
        } catch (final IOException e) {
            System.err.println("Could not read file " + args[0] + ":\n" + e);
            throw new KillAproveException(1);
        }
    }

    /**
     * Turns an intTRS into a T2 thingy.
     * @param intTrs some intTRS
     * @return a T2 transition system doing the same.
     */
    @SuppressWarnings("boxing")
    public static Pair<T2IntSys, Map<FunctionSymbol, Integer>> transformIntTRSToT2(final IRSProblem intTrs) {
        final Set<IGeneralizedRule> rules = intTrs.getRules(); // Get rules from TRS

        // First, normalize the rules to have the same number of arguments:
        // there is no need to track this procedure with regard to variable renaming
        final Triple<Map<FunctionSymbol, FunctionSymbol>, Map<FunctionSymbol, Integer>, Set<IGeneralizedRule>> triple =
            T2ExportTool.normalizeFs(rules);
        final Map<FunctionSymbol, FunctionSymbol> functionSymbolMap = triple.x;
        final Map<FunctionSymbol, Integer> pcMap = triple.y;
        final Set<IGeneralizedRule> normalizedRules = triple.z;
        final T2IntSys problem = new T2IntSys();

        if (intTrs.getStartTerm() != null) {
            FunctionSymbol rootSymbol = intTrs.getStartTerm().getRootSymbol();
            FunctionSymbol rootFunctionSymbol = functionSymbolMap.get(rootSymbol);
            Integer rootState = pcMap.get(rootFunctionSymbol);
            problem.setStartState(rootState);
        } else {
            //Add a start state:
            final FreshNameGenerator fne = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
            for (final Integer id : pcMap.values()) {
                fne.lockName(id.toString());
            }
            final int newStartState = Integer.valueOf(fne.getFreshName("0", false));

            for (final Integer id : pcMap.values()) {
                problem.addTransition(new T2IntTrans(newStartState, id, Collections.<T2IntTransBodyStatement>emptyList()));
            }

            problem.setStartState(newStartState);
        }

        // Now, handle each rule separately:
        CollectionMap<String, String> variableMapping = new CollectionMap<>();

        for (final IGeneralizedRule rule : normalizedRules) {
            IGeneralizedRule newRule = T2ExportTool.moveConstantMatchingToCond(rule);
            newRule = T2ExportTool.replaceFalseByOneEqualsZero(newRule);
            newRule = T2ExportTool.replaceTrueByZeroEqualsZero(newRule);
            Pair<T2IntTrans, CollectionMap<String, String>> transitionWithVariables = transformRuleToTransition(pcMap, newRule);
            problem.addTransition(transitionWithVariables.x);
            transitionWithVariables.y.forEach(variableMapping::add);
        }

        problem.setVariableRenaming(variableMapping);
        return new Pair<>(problem, pcMap);
    }

    private static IGeneralizedRule moveConstantMatchingToCond(final IGeneralizedRule rule) {
        final TRSFunctionApplication lhs = rule.getLeft();
        final FunctionSymbol lhsSym = lhs.getRootSymbol();
        final ArrayList<TRSTerm> args = new ArrayList<>(lhsSym.getArity());

        //Replace constants on the lhs, if needed:
        final FreshNameGenerator fne = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        fne.lockHasNames(rule.getVariables());
        TRSTerm newCond = rule.getCondTerm();
        
        for (final TRSTerm a : lhs.getArguments()) {
            // if the argument is TRS variable, append it to argument list directly
            if (a instanceof TRSVariable) {
                args.add(a);
            }
            // otherwise, create the TRS variable and append it to argument list
            else {
                final TRSVariable newVar = TRSTerm.createVariable(fne.getFreshName("x", false));
                newCond = IDPv2ToIDPv1Utilities.getConjunction(ToolBox.buildEq(newVar, a), newCond);
                args.add(newVar);
            }
        }

        return IGeneralizedRule.create(TRSTerm.createFunctionApplication(lhsSym, args), rule.getRight(), newCond);
    }
    
    private static IGeneralizedRule replaceFalseByOneEqualsZero(final IGeneralizedRule rule) {
        if (rule.getCondTerm() != null) {
            TRSTerm newCond = rule.getCondTerm().replaceAll(ToolBox.buildFalse(), TRSTerm.createFunctionApplication(FunctionSymbol.create("=", 2), TRSTerm.createConstant("0"), TRSTerm.createConstant("1")));
            return IGeneralizedRule.create(rule.getLeft(), rule.getRight(), newCond);
        } else {
            return rule;
        }
    }
    
    private static IGeneralizedRule replaceTrueByZeroEqualsZero(final IGeneralizedRule rule) {
        if (rule.getCondTerm() != null) {
            TRSTerm newCond = rule.getCondTerm().replaceAll(ToolBox.buildTrue(), TRSTerm.createFunctionApplication(FunctionSymbol.create("=", 2), TRSTerm.createConstant("0"), TRSTerm.createConstant("0")));
            return IGeneralizedRule.create(rule.getLeft(), rule.getRight(), newCond);
        } else {
            return rule;
        }
    }

    /** 
     * Try to infer an assignment for a given variable based on an equality condition in the condTerm.
     * This assignment may only use variables defined in usedVariables.
     * 
     * @param forVariable The variable to infer an assignment for
     * @param condTerm The condition term that can be used to infer an assignment
     * @param usedVariables The variables that can be used in the assignment of forVariable
     * @return An assignment for forVariable that is inferred from the condition term or null if 
     * no assignment could be inferred
     */
    private static T2IntTransAssignment inferAssignmentFromCondition(TRSVariable forVariable, TRSTerm condTerm, Set<TRSVariable> usedVariables) {
        if (condTerm instanceof TRSFunctionApplication) {
            TRSFunctionApplication compoundTerm = (TRSFunctionApplication) condTerm;
            String functionName = compoundTerm.getFunctionSymbol().getName();
            if (functionName.equals("&&")) {
                // Consider each subterm of a conjunction. If an assignment could be inferred from one
                // subterm, pick it and return
                for (TRSTerm term : compoundTerm.getArguments()) {
                    T2IntTransAssignment assignment = inferAssignmentFromCondition(forVariable, term, usedVariables);
                    if (assignment != null) {
                        return assignment;
                    }
                }
            } else if (functionName.equals("=") && compoundTerm.getVariables().contains(forVariable)) {
                // Check if the equality condition only contains variables that may be used
                // in forVariable's definition
                for (TRSVariable variable : compoundTerm.getVariables()) {
                    if (usedVariables.contains(variable)) {
                        continue;
                    } else if (variable == forVariable) {
                        continue;
                    } else {
                        return null;
                    }
                }
                TRSTerm rebasedTerm = IRSRearrange.rearrangeTermToVariable(compoundTerm, forVariable);
                if (rebasedTerm != null) {
                    return new T2IntTransAssignment(forVariable, rebasedTerm);
                }
            } else {
                return null;
            }
        }
        return null;
    }
    
    /**
     * Transform an intTRS-rule to a T2-style transition
     * @param pcMap a map from function symbol to integers
     * @param rule the rule that should be transformed
     * @return the resulting transition
     */
    private static Pair<T2IntTrans, CollectionMap<String, String>> transformRuleToTransition(
        final Map<FunctionSymbol, Integer> pcMap,
        final IGeneralizedRule rule) {
        CollectionMap<String, String> variableMapping = new CollectionMap<>();
        // IMPORTANT: Rename variables on the left to standard form:
        Pair<IGeneralizedRule, Map<TRSVariable, TRSVariable>> ruleWithXAndVariables = rule.getRenumberedRuleAndVariables("x");
        final IGeneralizedRule ruleWithX = ruleWithXAndVariables.x;
        final TRSFunctionApplication renamedLHS = ruleWithX.getLeft();
        ruleWithXAndVariables.y.forEach((fromVar, toVar) -> variableMapping.add(fromVar.getName(), toVar.getName()));
        // IMPORTANT: Rename variables a second time, to store away and use the original values:
        Pair<IGeneralizedRule, Map<TRSVariable, TRSVariable>> ruleWithOldXAndVariables = rule.getRenumberedRuleAndVariables("oldX");
        final IGeneralizedRule ruleWithOldX = ruleWithOldXAndVariables.x;
        final TRSFunctionApplication renamedOldLHS = ruleWithOldX.getLeft();
        final TRSFunctionApplication renamedOldRHS = (TRSFunctionApplication) ruleWithOldX.getRight();
        ruleWithOldXAndVariables.y.forEach((fromVar, toVar) -> variableMapping.add(fromVar.getName(), toVar.getName()));
        //First step: Store values to oldX
        final List<T2IntTransBodyStatement> transitionStatements = new LinkedList<>();
        final ImmutableList<TRSTerm> varsWithX = renamedLHS.getArguments();
        final ImmutableList<TRSTerm> varsWithOldX = renamedOldLHS.getArguments();
        Set<TRSVariable> variablesAssignedValue = new HashSet<>();
        for (int i = 0; i < varsWithOldX.size(); i++) {
            transitionStatements.add(new T2IntTransAssignment((TRSVariable) varsWithOldX.get(i), varsWithX.get(i)));
            variablesAssignedValue.add((TRSVariable) varsWithOldX.get(i));
        }
        //Second step: Set fresh variables to random values:
        final Set<TRSVariable> usedVariables = new LinkedHashSet<>(ruleWithOldX.getVariables());
        if (ruleWithOldX.getCondTerm() != null) {
            usedVariables.addAll(ruleWithOldX.getCondVariables());
        }

        final List<TRSTerm> newValuesComputedUsingOldX = new ArrayList<>(renamedOldRHS.getArguments());
        boolean addedAssignment = false;

        do {
            addedAssignment = false;
            for (final TRSVariable v : usedVariables) {
                //Skip if variable is already set
                if (variablesAssignedValue.contains(v)) {
                    continue;
                }
                T2IntTransAssignment assignment = inferAssignmentFromCondition(v, ruleWithOldX.getCondTerm(), variablesAssignedValue);
                if (assignment != null) {
                    int index = newValuesComputedUsingOldX.indexOf(v);
                    transitionStatements.add(assignment);
                    variablesAssignedValue.add(v);
                    addedAssignment = true;
                    if (index != -1) {
                        newValuesComputedUsingOldX.set(index, assignment.getValue());
                    }
                }
            }
        } while (addedAssignment);

        for (final TRSVariable v : usedVariables) {
            //Skip if variable is bound (i.e., gets set before):
            if (variablesAssignedValue.contains(v)) {
                continue;
            }
            transitionStatements.add(new T2IntTransRandAssignment(v));
        }
        //Third step: Assume the guard, if there is one:
        final TRSTerm cond = ruleWithOldX.getCondTerm();
        if (cond != null) {
            transitionStatements.add(new T2IntTransGuard(cond));
        }
        //Fourth step: Add the variable updates:
        for (int i = 0; i < varsWithX.size(); i++) {
            transitionStatements.add(new T2IntTransAssignment((TRSVariable) varsWithX.get(i), newValuesComputedUsingOldX
                .get(i)));
        }
        //Get the transition start and end (remove the additional PC argument for the map...):
        final Integer start = pcMap.get(renamedOldLHS.getRootSymbol());
        final Integer end = pcMap.get(renamedOldRHS.getRootSymbol());


        return new Pair<>(new T2IntTrans(start, end, transitionStatements), variableMapping);
    }

    /**
     * Chooses a map m from existing function symbols to an integer. Then turns rules
     * like
     *  f(x1, ..., xn) -> g(t1, ..., tm) | c
     * into a new rule
     *  f(x1, ..., xn, y1 ..., yk) -> g(t1, ..., tm, z1, ..., zl) | c
     * such that n + k = argNum and m + l = argNum holds, where argnum is maximal number of arguments occurring.
     * @param rules some rules
     * @return a triple mapping the old FS to the new FS, the new FS to an integer id and the modified rules
     */
    public static Triple<Map<FunctionSymbol, FunctionSymbol>, Map<FunctionSymbol, Integer>, Set<IGeneralizedRule>> normalizeFs(final Set<IGeneralizedRule> rules)
    {
        final Map<FunctionSymbol, FunctionSymbol> functionSymbolMap = new LinkedHashMap<>(); // Mapping from existing function symbol to newly created function symbol
        final Map<FunctionSymbol, Integer> functionSymbolIndexMap = new LinkedHashMap<>(); // Mapping from function symbol to the index
        int maximumArity = getMaximumArity(rules);

        int index = 0;
        for (final IGeneralizedRule rule : rules) {
            final FunctionSymbol lhsRootFuncSym = rule.getRootSymbol();
            final FunctionSymbol newLhsRootFuncSym = FunctionSymbol.create(lhsRootFuncSym.getName(), maximumArity);

            // if the function symbol does not exist in the index map, add it into the map
            if (!functionSymbolIndexMap.containsKey(newLhsRootFuncSym)) {
                functionSymbolMap.put(lhsRootFuncSym, newLhsRootFuncSym);
                functionSymbolIndexMap.put(newLhsRootFuncSym, ++index);
            }

            final TRSTerm rhs = rule.getRight();
            if (!rhs.isVariable()) {
                final FunctionSymbol rhsRootFuncSym = ((TRSFunctionApplication) rhs).getRootSymbol();
                final FunctionSymbol newRhsRootFuncSym = FunctionSymbol.create(rhsRootFuncSym.getName(), maximumArity);

                // if the function symbol does not exist in the index map, add it into the map
                if (!functionSymbolIndexMap.containsKey(newRhsRootFuncSym)) {
                    functionSymbolMap.put(rhsRootFuncSym, newRhsRootFuncSym);
                    functionSymbolIndexMap.put(newRhsRootFuncSym, ++index);
                }
            }
        }

        final Set<IGeneralizedRule> newRules = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : rules) {
            newRules.add(normalizeRule(rule, maximumArity));
        }

        return new Triple<>(functionSymbolMap, functionSymbolIndexMap, newRules);
    }

    /**
     * Get the maximum arity over all transition rules in a set
     *
     * @param rules transition rules to be processed
     * @return the maximum arity over all transition rules in a set
     */
    private static int getMaximumArity(Set<IGeneralizedRule> rules) {
        int maximumArity = 0;

        for (final IGeneralizedRule rule : rules) {
            final FunctionSymbol lhsRootFuncSym = rule.getRootSymbol();
            maximumArity = Math.max(maximumArity, lhsRootFuncSym.getArity());

            if (rule.getRight() instanceof TRSFunctionApplication) {
                final TRSFunctionApplication rhsFuncAppl = (TRSFunctionApplication) rule.getRight();
                maximumArity = Math.max(maximumArity, rhsFuncAppl.getArity());
            }
        }

        return maximumArity;
    }


    /**
     * @param rule Some rule f(x1, ..., xn) -> g(t1, ..., tm) | c
     * @param argNum number of arguments every term should have after we are done. Should be at
     *  least the max of the arity of all occurring defined symbols
     * @return a new rule f(x1, ..., xn, y1 ..., yk) -> g(t1, ..., tm, z1, ..., zl) | c
     *  such that n + k = argNum and m + l = argNum holds
     */
    private static IGeneralizedRule normalizeRule(final IGeneralizedRule rule, final int argNum) {
        final TRSFunctionApplication lhs = rule.getLeft();
        final TRSTerm rhs = rule.getRight();
        final TRSTerm cond = rule.getCondTerm();

        final FreshNameGenerator fne = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        fne.lockHasNames(lhs.getVariables());

        final FunctionSymbol lhsFs = lhs.getRootSymbol();
        if (Globals.useAssertions) {
            assert (lhsFs.getArity() <= argNum) : "FS has more arguments than allowed";
        }

        // the name of new left-hand arguments starts with y
        final ArrayList<TRSTerm> newLhsArgs = new ArrayList<>(argNum);
        newLhsArgs.addAll(lhs.getArguments());
        for (int i = newLhsArgs.size(); i < argNum; i++) {
            newLhsArgs.add(TRSTerm.createVariable(fne.getFreshName("y", false)));
        }
        final TRSFunctionApplication newLhs =
            TRSTerm.createFunctionApplication(FunctionSymbol.create(lhsFs.getName(), argNum), newLhsArgs);

        if (Globals.useAssertions) {
            assert (!rhs.isVariable()) : "intTRS with rhs just a variable. Help!";
        }

        final TRSFunctionApplication rhsFA = (TRSFunctionApplication) rhs;
        final FunctionSymbol rhsFs = rhsFA.getRootSymbol();
        if (Globals.useAssertions) {
            assert (rhsFs.getArity() <= argNum) : "FS has more arguments than allowed";
        }

        // the name of new right-hand arguments starts with z
        final ArrayList<TRSTerm> newRhsArgs = new ArrayList<>(argNum);
        newRhsArgs.addAll(rhsFA.getArguments());
        for (int i = newRhsArgs.size(); i < argNum; i++) {
            newRhsArgs.add(TRSTerm.createVariable(fne.getFreshName("z", false)));
        }
        final TRSFunctionApplication newRhs =
            TRSTerm.createFunctionApplication(FunctionSymbol.create(rhsFs.getName(), argNum), newRhsArgs);

        return IGeneralizedRule.create(newLhs, newRhs, cond);
    }
}
