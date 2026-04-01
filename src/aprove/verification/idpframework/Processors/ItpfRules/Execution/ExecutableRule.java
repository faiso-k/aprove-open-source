package aprove.verification.idpframework.Processors.ItpfRules.Execution;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import immutables.*;

/**
 *
 * @author MP
 */
public interface ExecutableRule<FormulaType extends ProcessableFormula, MarkMetaData> extends IDPExportable, Mark<MarkMetaData>, Immutable {

    /**
     * @return True iff rule is sound;
     */
    public boolean isSound();

    /**
     * @return True iff rule is complete;
     */
    public boolean isComplete();

    /**
     * this is a fast test whether this processor can in general handle the
     * given IDP.
     */
    public boolean isApplicable(IDPProblem idp);

    /**
     * this is a fast test whether this processor can in general handle a given
     * ITPS-formula.
     */
    public boolean isApplicable(IDPProblem idp,
        FormulaType formula,
        ApplicationMode mode);

    /**
     * Computes the result of this processor applied to a formula.
     * @param idp - the idp problem the formula belongs to
     * @param formula - the formula
     * @param executionRequirements
     * @param aborter - the aborter, that should be checked many times against
     * timeouts/aborts, ...
     * @return The result of this processor
     * @throws AbortionException
     */
    public ExecutionResult<Conjunction<FormulaType>, FormulaType> process(final IDPProblem idp,
        final FormulaType formula,
        final ImplicationType executionRequirements, final ApplicationMode mode,
        final Abortion aborter) throws AbortionException;

    public Collection<? extends Mark<?>> getUsedMarks();

}
