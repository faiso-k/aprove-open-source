/**
 * @author thetux
 * @version $Id$
 */

package aprove.verification.dpframework.Heuristics.RootLabeling;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * All function symbols will get labeled with all parameters
 *
 * @author Andreas Kelle-Emden
 */
public class LabelAllHeuristic implements RootLabelingHeuristic {

    @Override
    public Map<FunctionSymbol, Set<Integer>> getLabelMap(Set<Rule> R, Set<Rule> P,
            Set<FunctionSymbol> symbolsF, Set<FunctionSymbol> symbolsFHash,
            Set<FunctionSymbol> symbolsFR, Set<FunctionSymbol> symbolsFP,
            FunctionSymbol symDelta, int proc) {

        Map<FunctionSymbol, Set<Integer>> map = new LinkedHashMap<FunctionSymbol, Set<Integer>>();
        switch(proc) {
        case 0:
            // Plain root labeling: label all symbols in R
            for (FunctionSymbol func : symbolsFR) {
                int arity = func.getArity();
                if (arity > 0) {
                    Set<Integer> parms = new LinkedHashSet<Integer>();
                    for (int i = 0; i < arity; i++) {
                        parms.add(i);
                    }
                    map.put(func, parms);
                }
            }
            return map;
            //break;
        case 1:
            // FC1: Label all symbols that are not root symbols in P
            for (FunctionSymbol func : symbolsF) {
                int arity = func.getArity();
                if (arity > 0) {
                    Set<Integer> parms = new LinkedHashSet<Integer>();
                    for (int i = 0; i < arity; i++) {
                        parms.add(i);
                    }
                    map.put(func, parms);
                }
            }
            if (Options.certifier.isCpf()) {
                for (FunctionSymbol func : symbolsFHash) {
                    int arity = func.getArity();
                    if (arity > 0) {
                        Set<Integer> parms = new LinkedHashSet<Integer>();
                        for (int i = 0; i < arity; i++) {
                            parms.add(i);
                        }
                        map.put(func, parms);
                    }
                }
            }
            return map;
            //break;
        case 2:
            // FC2: Label all symbols occuring in P or R
            for (FunctionSymbol func : symbolsF) {
                int arity = func.getArity();
                if (arity > 0) {
                    Set<Integer> parms = new LinkedHashSet<Integer>();
                    for (int i = 0; i < arity; i++) {
                        parms.add(i);
                    }
                    map.put(func, parms);
                }
            }
            for (FunctionSymbol func : symbolsFHash) {
                int arity = func.getArity();
                if (arity > 0) {
                    Set<Integer> parms = new LinkedHashSet<Integer>();
                    for (int i = 0; i < arity; i++) {
                        parms.add(i);
                    }
                    map.put(func, parms);
                }
            }
            return map;
            //break;
        }
        return null;
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
        return true;
    }

    @Override
    public String export(Export_Util eu, Map<FunctionSymbol, Set<Integer>> labelMap) {
        return "LabelAll: All function symbols get labeled" + eu.newline();
    }
}
