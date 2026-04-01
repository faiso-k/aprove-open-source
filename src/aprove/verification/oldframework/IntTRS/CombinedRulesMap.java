package aprove.verification.oldframework.IntTRS;

import java.util.*;

import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Similar to the Interface VariableRenaming, this interface demands a map to be saved.
 * This time, the original rules of a combined rule are stored.
 * 
 * @author cMensendiek
 */
public interface CombinedRulesMap {

    /**
     * Get map of a combined rule and the two rules it originated from
     *
     * @return the corresponding map
     */
    Map<IGeneralizedRule, Pair<IGeneralizedRule,IGeneralizedRule>> getCombinedRulesMap();

    /**
     * Set map of a combined rule and the two rules it originated from
     *
     * @param map map of AbstractStates to FunctionSymbol
     */
    void setCombinedRulesMap(Map<IGeneralizedRule, Pair<IGeneralizedRule,IGeneralizedRule>> map);
    
}