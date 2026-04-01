package aprove.verification.oldframework.Utility.Profiling.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class TRSProperties {
    public enum Properties {
        /** the maximal arity of any function symbol */
        MaxArity,
        /** the average arity of all function symbols */
        AvgArity,
        /** the maximal depth of any lhs */
        MaxDepthLeft,
        /** the maximal depth of any rhs */
        MaxDepthRight,
        /** maximal number of distinct variables in any rule */
        MaxDistinctVarsInRule,
        /**
         * Consider a rule containing the variable x n times in its lhs and m
         * times in its rhs. Then the duplicating factor of this variable in
         * this rule is m/n. This function returns the maximal duplication
         * factor for any variable and rule. Times 100 to be useful as an
         * integer.
         */
        MaxDuplicatingFactor,
        /** the maximal number of occurrences of a variable in any lhs */
        MaxNonLinearityDegreeLeft,
        /** the maximal number of occurrences of a variable in any rhs */
        MaxNonLinearityDegreeRight,
        /** size of sigma */
        NumOfDifferentSymbols,
        /** number of rules */
        NumOfRules,
        /** absolute number of function symbols and variables in a system */
        Size,
        /** Number of different (modulo renaming of variables) subterms */
        NumOfDifferentSubterms,
        /** Number of defined symbols */
        NumOfDefinedSyms,
        /** Number of rules where rhs embeds lhs */
        NumOfRhsEmbedLhs,
        /** number of occurences of function symbols */
        NumOfOccurFunctionSymbols,
        /** number of occurences of variables */
        NumOfOccurVariables,
        /** max occurences of a function symbol */
        MaxOccurFunctionSymbol
    }

    public static EnumMap<Properties, Integer> computeProperties(Iterable<? extends GeneralizedRule> rules) {
        int maxArity = 0;
        int avgArity = 0;
        int maxDepthLeft = 0;
        int maxDepthRight = 0;
        int maxNonLinearityDegreeRight = 0;
        int maxNonLinearityDegreeLeft = 0;
        int maxDuplicatingFactor = 0;
        int numOfRules = 0;
        int size = 0;
        int maxDistinctVarsInRule = 0;
        int numOfRhsEmdedLhs = 0;
        int numOfOccurFunctionSymbols = 0;
        int numOfOccurVariables = 0;
        int maxOccurFunctionSymbol = 0;
        MultiSet<FunctionSymbol> occurFunSyms =
            new HashMultiSet<FunctionSymbol>();

        Set<FunctionSymbol> sigma = new LinkedHashSet<FunctionSymbol>();
        Set<TRSTerm> subterms = new LinkedHashSet<TRSTerm>();
        Set<FunctionSymbol> definedSymbols =
            new LinkedHashSet<FunctionSymbol>();

        for (GeneralizedRule r : rules) {
            definedSymbols.add(r.getRootSymbol());
            ++numOfRules;
            TRSTerm left = r.getLeft();
            TRSTerm right = r.getLeft();
            Map<TRSVariable, Integer> leftVars = left.getVariableCount();
            Map<TRSVariable, Integer> rightVars = right.getVariableCount();
            Set<TRSVariable> vars = new HashSet<TRSVariable>();
            vars.addAll(leftVars.keySet());
            vars.addAll(rightVars.keySet());
            for (Map.Entry<TRSVariable, Integer> e : leftVars.entrySet()) {
                TRSVariable v = e.getKey();
                Integer leftcount = e.getValue();
                if (rightVars.containsKey(v)) {
                    Integer rightcount = rightVars.get(v);
                    maxDuplicatingFactor =
                        Math.max(maxDuplicatingFactor, 100 * rightcount
                            / leftcount);
                }
            }
            maxDepthLeft = Math.max(maxDepthLeft, left.getDepthConstant());
            maxDepthRight = Math.max(maxDepthRight, right.getDepthConstant());
            if (!leftVars.values().isEmpty()) {
                maxNonLinearityDegreeLeft =
                    Math.max(maxNonLinearityDegreeLeft,
                        java.util.Collections.max(leftVars.values()));
            }
            if (!rightVars.isEmpty()) {
                maxNonLinearityDegreeRight =
                    Math.max(maxNonLinearityDegreeRight,
                        java.util.Collections.max(rightVars.values()));
            }
            sigma.addAll(r.getFunctionSymbols());
            size += left.getSize() + right.getSize();
            maxDistinctVarsInRule =
                Math.max(maxDistinctVarsInRule, vars.size());

            for (TRSTerm t : IterableConcatenator.create(left.getSubTerms(),
                right.getSubTerms())) {
                subterms.add(t.getStandardRenumbered());
            }

            if (right.hasSubterm(left)) {
                numOfRhsEmdedLhs += 1;
            }

            numOfOccurFunctionSymbols += TRSProperties.computeOccurencesFunSym(right);
            numOfOccurFunctionSymbols += TRSProperties.computeOccurencesFunSym(left);
            numOfOccurVariables += TRSProperties.computeOccurencesVariables(right);
            numOfOccurVariables += TRSProperties.computeOccurencesVariables(left);

            occurFunSyms.add(((TRSFunctionApplication) left).getRootSymbol());
        }

        for (FunctionSymbol f : sigma) {
            maxArity = Math.max(maxArity, f.getArity());
            avgArity += f.getArity();
        }

        for (FunctionSymbol f : occurFunSyms.toList()) {
            maxOccurFunctionSymbol =
                Math.max(maxOccurFunctionSymbol, occurFunSyms.get(f));
        }

        if (sigma.size() != 0) {
            avgArity *= 100; // to get reasonable results
            avgArity /= sigma.size();
        }

        Map<Properties, Integer> map = new LinkedHashMap<Properties, Integer>();

        map.put(Properties.MaxArity, maxArity);
        map.put(Properties.AvgArity, avgArity);
        map.put(Properties.MaxDepthLeft, maxDepthLeft);
        map.put(Properties.MaxDepthRight, maxDepthRight);
        map.put(Properties.MaxDuplicatingFactor, maxDuplicatingFactor);
        map.put(Properties.MaxNonLinearityDegreeLeft, maxNonLinearityDegreeLeft);
        map.put(Properties.MaxNonLinearityDegreeRight,
            maxNonLinearityDegreeRight);
        map.put(Properties.NumOfRules, numOfRules);
        map.put(Properties.NumOfDifferentSymbols, sigma.size());
        map.put(Properties.Size, size);
        map.put(Properties.NumOfDifferentSubterms, subterms.size());
        map.put(Properties.MaxDistinctVarsInRule, maxDistinctVarsInRule);
        map.put(Properties.NumOfDefinedSyms, definedSymbols.size());
        map.put(Properties.NumOfRhsEmbedLhs, numOfRhsEmdedLhs);
        map.put(Properties.NumOfOccurFunctionSymbols, numOfOccurFunctionSymbols);
        map.put(Properties.NumOfOccurVariables, numOfOccurVariables);
        map.put(Properties.MaxOccurFunctionSymbol, maxOccurFunctionSymbol);

        return new EnumMap<Properties, Integer>(map);
    }

    private static int computeOccurencesFunSym(TRSTerm term) {
        int count = 0;

        for (TRSTerm t : term) {
            if (!t.isVariable()) {
                count += 1;
            }
        }
        return count;
    }

    private static int computeOccurencesVariables(TRSTerm term) {
        int count = 0;

        for (TRSTerm t : term) {
            if (t.isVariable()) {
                count += 1;
            }
        }
        return count;
    }

}