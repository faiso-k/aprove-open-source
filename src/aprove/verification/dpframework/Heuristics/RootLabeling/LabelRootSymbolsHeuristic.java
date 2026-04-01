/**
 * @author thetux
 * @version $Id$
 */

package aprove.verification.dpframework.Heuristics.RootLabeling;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Label only function symbols that are root symbols in P
 *
 * @author Andreas Kelle-Emden
 */
public class LabelRootSymbolsHeuristic implements RootLabelingHeuristic {

    @Override
    public Map<FunctionSymbol, Set<Integer>> getLabelMap(Set<Rule> R, Set<Rule> P,
            Set<FunctionSymbol> symbolsF, Set<FunctionSymbol> symbolsFHash,
            Set<FunctionSymbol> symbolsFR, Set<FunctionSymbol> symbolsFP,
            FunctionSymbol symDelta, int proc) {

        Map<FunctionSymbol, Set<Integer>> map = new LinkedHashMap<FunctionSymbol, Set<Integer>>();
        // Only symbols in FHash get labeled
        for (FunctionSymbol func : symbolsFHash) {
            int arity = func.getArity();
            Set<Integer> parms = new LinkedHashSet<Integer>();
            for (int i = 0; i < arity; i++) {
                parms.add(i);
            }
            map.put(func, parms);
        }
        return map;
    }

    @Override
    public boolean isFC1Applicable() {
        return false;
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
        return "LabelRootSymbols: Only function symbols that occur as root symbols in P get labeled" + eu.newline();
    }

}
