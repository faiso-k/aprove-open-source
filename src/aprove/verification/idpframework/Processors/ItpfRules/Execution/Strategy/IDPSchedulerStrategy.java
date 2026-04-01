package aprove.verification.idpframework.Processors.ItpfRules.Execution.Strategy;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 *
 * @author Martin Pluecker
 */
public interface IDPSchedulerStrategy<FormulaType extends ProcessableFormula, RuleType extends ExecutableRule<FormulaType, ?>> {

    /**
     * @param proof The current proof providing also the formula to process
     * (@see{ItpfSchedulerProof#getLastFormulaState}). All changes will be
     * registered in the proof.
     * @param aborter TODO
     * @return x : True if execution has been successfull, y: new strategy to be
     * executed or null if strategy is complete.
     * @throws AbortionException TODO
     */
    public Pair<Boolean, IDPSchedulerStrategy<FormulaType, RuleType>> apply(ItpfSchedulerProof<FormulaType, RuleType> proof, ImplicationType executionRequirements, Abortion aborter) throws AbortionException;

    /**
     * @return All rules occuring in this strategy
     */
    public Set<RuleType> getAllRules();

}
