package aprove.verification.dpframework.IDPProblem.Processors.algorithms.filter;

import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public interface IIDPFilterHeuristic extends IDPExportable {

    /**
     * @param interpretation
     * @param f
     */
    public ImmutableCollection<Integer> getFilteredPositions(IDPRuleAnalysis ruleAnalysis, FunctionSymbol f);

}
