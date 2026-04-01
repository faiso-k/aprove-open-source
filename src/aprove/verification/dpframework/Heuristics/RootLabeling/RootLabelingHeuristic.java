package aprove.verification.dpframework.Heuristics.RootLabeling;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Interface for root labeling heuristics
 *
 * @author Andreas Kelle-Emden
 */
public interface RootLabelingHeuristic {

    /**
     * Is this heuristic applicable for plain root labeling?
     */
    public boolean isRLApplicable();

    /**
     * Is this heuristic applicable for FC1 root labeling?
     */
    public boolean isFC1Applicable();

    /**
     * Is this heuristic applicable for FC2 root labeling?
     */
    public boolean isFC2Applicable();

    /**
     * Calculate the list of function symbols which will get labeled.
     * We assign to every function symbol a list of parameter numbers which
     * will be used for the labeling.
     *
     * @param R Rules in R
     * @param P Rules in P
     * @param symbolsF Set of symbols in F
     * @param symbolsFHash Set of symbols in FHash
     * @param symbolsFR Set of symbols occuring in R
     * @param symbolsFP Set of symbols occuring in P
     * @param proc Which processor called this method? 0 is plain root labeling,
     *        1 and 2 are root labeling on DP problems (FC1 or FC2 respectively)
     * @param symDelta the DELTA symbol for FC1
     * @return Map of function symbols to list of parameter numbers
     */
    public Map<FunctionSymbol, Set<Integer>> getLabelMap(
            Set<Rule> R,
            Set<Rule> P,
            Set<FunctionSymbol> symbolsF,
            Set<FunctionSymbol> symbolsFHash,
            Set<FunctionSymbol> symbolsFR,
            Set<FunctionSymbol> symbolsFP,
            FunctionSymbol symDelta,
            int proc);

    public String export(Export_Util eu, Map<FunctionSymbol, Set<Integer>> labelMap);



}
