package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import immutables.*;

/**
 * @author MP
 */
public class ItpfImplicationSplit<C extends SemiRing<C>> extends
    ContextFreeItpfReplaceRule {

    public ItpfImplicationSplit() {
        super(new ExportableString("ItpfImplicationSplit"),
            new ExportableString("ItpfImplicationSplit"));
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
        return idp.getIdpGraph().getPolyInterpretation() != null;
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
        return false;
    }

    @Override
    public boolean isContextFree() {
        return true;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return this.equals(mark);
    }

    @Override
    public Collection<? extends Mark<?>> getUsedMarks() {
        return Collections.<Mark<?>> singleton(this);
    }

    @Override
    protected ExecutionResult<? extends QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processImplication(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfImplication implication,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException {

        if (implication.getPrecondition().getClauses().size() > 1 && positive
            && !mode.isNoOp()) {
            final ItpfFactory itpfFactory = idp.getItpfFactory();

            final LiteralMap newImplications = new LiteralMap();

            for (final ItpfConjClause precondClause : implication.getPrecondition().getClauses()) {
                newImplications.put(
                    itpfFactory.createImplication(
                        itpfFactory.create(precondClause),
                        implication.getConclusion()), true);
            }

            return this.createReplaceData(itpfFactory, ItpfFactory.EMPTY_QUANTORS,
                newImplications, ImplicationType.EQUIVALENT, ApplicationMode.SingleStep, false);
        } else if (implication.getPrecondition().getClauses().size() > 1
            && !positive && !mode.isNoOp()) {
            final ItpfFactory itpfFactory = idp.getItpfFactory();

            final List<ItpfAtomReplaceData> replaceData =
                new ArrayList<ItpfAtomReplaceData>();

            for (final ItpfConjClause precondClause : implication.getPrecondition().getClauses()) {
                final ItpfImplication newImplication =
                    itpfFactory.createImplication(
                        itpfFactory.create(precondClause),
                        implication.getConclusion());
                final ItpfAtomReplaceData replace =
                    new ItpfAtomReplaceData.LiteralMapData(
                        new LiteralMap(newImplication, false),
                        ITerm.EMPTY_SET);
                replaceData.add(replace);
            }

            return new ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData>(
                new QuantifiedDisjunction<ItpfAtomReplaceData>(ItpfFactory.EMPTY_QUANTORS, ImmutableCreator.create(replaceData)),
                ImplicationType.EQUIVALENT, ApplicationMode.SingleStep, false);
        } else {
            return super.processImplication(idp, context, precondition, s,
                implication, positive, executionRequirements, mode, aborter);
        }
    }

    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode, final Abortion aborter) {
        // nothing to do here
        return null;
    }
}
