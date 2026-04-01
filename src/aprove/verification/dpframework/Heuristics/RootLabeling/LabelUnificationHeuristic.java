package aprove.verification.dpframework.Heuristics.RootLabeling;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Use label unification to determine which function symbols should get labeled
 *
 * @author Andreas Kelle-Emden
 */
public class LabelUnificationHeuristic implements RootLabelingHeuristic {

    @Override
    public Map<FunctionSymbol, Set<Integer>> getLabelMap(Set<Rule> R,
            Set<Rule> P, Set<FunctionSymbol> symbolsF,
            Set<FunctionSymbol> symbolsFHash, Set<FunctionSymbol> symbolsFR,
            Set<FunctionSymbol> symbolsFP, FunctionSymbol symDelta, int proc) {


        // Check if all rules are root preserving
        for (Rule rule : R) {
            TRSTerm tr = rule.getRight();
            if (tr.isVariable()) {
                return null;
            }
            TRSFunctionApplication fal = rule.getLeft();
            TRSFunctionApplication far = (TRSFunctionApplication)tr;
            FunctionSymbol syml = fal.getRootSymbol();
            FunctionSymbol symr = far.getRootSymbol();
            if (!syml.equals(symr)) {
                return null;
            }
        }
        if (P != null) {
            for (Rule rule : P) {
                TRSTerm tr = rule.getRight();
                if (tr.isVariable()) {
                    return null;
                }
                TRSFunctionApplication fal = rule.getLeft();
                TRSFunctionApplication far = (TRSFunctionApplication)tr;
                FunctionSymbol syml = fal.getRootSymbol();
                FunctionSymbol symr = far.getRootSymbol();
                if (!syml.equals(symr)) {
                    return null;
                }
            }
        }

        // Create empty clash map
        Map<FunctionSymbol, FunctionSymbol[]> clashMap = new LinkedHashMap<FunctionSymbol, FunctionSymbol[]>();

        Set<FunctionSymbol> symbolsAll = new LinkedHashSet<FunctionSymbol>(symbolsF);
        symbolsAll.addAll(symbolsFHash);

        for (FunctionSymbol sym : symbolsAll) {
            int arity = sym.getArity();
            FunctionSymbol[] arr = new FunctionSymbol[arity];
            for (int i = 0; i < arity; i++) {
                arr[i] = null;
            }
            clashMap.put(sym, arr);
        }

        // collect clashes in R
        for (Rule rule : R) {
            TRSFunctionApplication l = rule.getLeft();
            TRSTerm r = rule.getRight();

            RootLabelingUtility.collectClashes(l, r, clashMap);
        }

        // collect clashes in P, if available
        if (P != null) {
            for (Rule rule : P) {
                TRSFunctionApplication l = rule.getLeft();
                TRSTerm r = rule.getRight();

                RootLabelingUtility.collectClashes(l, r, clashMap);
            }
        }

        // Build label map from clash map
        Map<FunctionSymbol, Set<Integer>> labelMap = new LinkedHashMap<FunctionSymbol, Set<Integer>>();

        for (Map.Entry<FunctionSymbol, FunctionSymbol[]> e : clashMap.entrySet()) {
            FunctionSymbol sym = e.getKey();
            FunctionSymbol[] arr = e.getValue();
            int arity = sym.getArity();
            Set<Integer> set = new LinkedHashSet<Integer>();
            for (int i = 0; i < arity; i++) {
                if (arr[i] == RootLabelingUtility.clash) {
                    // We have a clash here!
                    set.add(i);
                }
            }
            if (!set.isEmpty()) {
                labelMap.put(sym, set);
            }
        }


        // if no symbol clashes, return null
        if (labelMap.isEmpty()) {
            return null;
        }

        return labelMap;
    }

    @Override
    public boolean isFC1Applicable() {
        return true;
    }

    @Override
    public boolean isFC2Applicable() {
        return true;
    }

    @Override
    public boolean isRLApplicable() {
        return false;
    }

    @Override
    public String export(Export_Util eu, Map<FunctionSymbol, Set<Integer>> labelMap) {
        StringBuilder s = new StringBuilder();
        s.append ("LabelUnification: Try label unification on all rules and label only clashing symbols" + eu.newline());
        s.append ("The following symbols get labeled:" + eu.newline());
        for (Map.Entry<FunctionSymbol, Set<Integer>> e : labelMap.entrySet()) {
            Set<Integer> set = e.getValue();
            FunctionSymbol sym = e.getKey();
            s.append (sym + ": " + set.toString() + eu.newline());
        }
        s.append(eu.newline());
        return s.toString();
    }
}
