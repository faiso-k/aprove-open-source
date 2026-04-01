package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import immutables.*;

/**
 * @author MP
 */
public class ItpfTrivialImplication extends AbstractItpfReplaceRule<ReplaceContext.ReplaceContextSkeleton, ItpfConjClause, Unused> {

    public ItpfTrivialImplication() {
        super(new ExportableString("ItpfTrivialImplication"), new ExportableString("ItpfTrivialImplication"));
    }

    @Override
    public boolean isSound() {
        return true;
    }

    @Override
    public boolean isComplete() {
        return true;
    }

    @Override
    public boolean isApplicable(final IDPProblem idp) {
        return true;
    }

    @Override
    public boolean isApplicable(final IDPProblem idp,
        final Itpf formula,
        final ApplicationMode mode) {
        return this.isApplicable(idp);
    }

    @Override
    public boolean isAtomicMark() {
        return false;
    }

    @Override
    public boolean isClauseMark() {
        return true;
    }

    @Override
    public boolean isContextFree() {
        return true;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return CompatibleMarkClasses.I_TRIVIAL_IMPLICATION.isCompatible(mark);
    }

    @Override
    public Collection<? extends Mark<?>> getUsedMarks() {
        return Collections.<Mark<?>> singleton(this);
    }

    @Override
    protected aprove.verification.idpframework.Processors.ItpfRules.ReplaceContext.ReplaceContextSkeleton createContext(final IDPProblem idp,
        final ItpfAndWrapper precondition,
        final Itpf formula,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {
        return new ReplaceContext.ReplaceContextSkeleton();
    }

    @Override
    protected ExecutionResult<? extends QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause> processImplication(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfImplication implication,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException {

        if (implication.getPrecondition().isFalse() || implication.getConclusion().isTrue()) {
            if (positive) {
                return this.getEmptyReturn(idp.getItpfFactory(), ImplicationType.EQUIVALENT, ApplicationMode.SingleStep);
            } else {
                return this.getUnsatReturn(ImplicationType.EQUIVALENT, ApplicationMode.SingleStep);
            }
        } else if (implication.getPrecondition().isTrue() & positive) {
            final ExecutionResult<Conjunction<Itpf>, Itpf> conclusionResult =
                this.process(idp, precondition, implication.getConclusion(), executionRequirements, mode.decreaseBy(ApplicationMode.SingleStep), aborter);
            final ItpfFactory itpfFactory = idp.getItpfFactory();

            final Itpf totalConclusion = itpfFactory.createAnd(conclusionResult.asCollection());

            return new ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>(totalConclusion, ImplicationType.EQUIVALENT, conclusionResult.usedApplications.increaseOneStep(), conclusionResult.fixpointReached);
        } else {
            return super.processImplication(idp, context, precondition, s, implication, positive, executionRequirements, mode, aborter);
        }
    }

    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause> processLiteral(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {
        return null;
    }

    @Override
    protected ItpfConjClause createReplaceData(final ItpfFactory itpfFactory,
        final LiteralMap conjunction, final ImmutableSet<ITerm<?>> sTerms) {
        return itpfFactory.createClause(ImmutableCreator.create(conjunction), ITerm.EMPTY_SET);
    }


}
