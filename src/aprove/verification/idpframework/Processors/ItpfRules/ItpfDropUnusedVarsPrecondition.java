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
 *
 * @author MP
 */
public class ItpfDropUnusedVarsPrecondition extends ContextFreeItpfReplaceRule {

    public ItpfDropUnusedVarsPrecondition() {
        super(new ExportableString("[i] DropUnusedVarsPrecondition"), new ExportableString("[i] DropUnusedVarsPrecondition"));
    }

    @Override
    public boolean isSound() {
        return true;
    }

    @Override
    public boolean isComplete() {
        return false;
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
    public Collection<Mark<Unused>> getUsedMarks() {
        return Collections.<Mark<Unused>> singleton(this);
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
        if (!executionRequirements.isSound()) {
            final ExecutionResult<Conjunction<Itpf>, Itpf> processedConclusion =
                this.process(idp, implication.getConclusion(), executionRequirements, mode, aborter);

            ApplicationMode remainingApplications = mode.decreaseBy(processedConclusion.usedApplications);
            ApplicationMode usedApplications = processedConclusion.usedApplications;
            ImplicationType totalImplication = processedConclusion.implication;

            final Set<IVariable<?>> conclusionVariables = CollectionUtil.getMarkVariables(processedConclusion.asCollection());

            final ItpfFactory itpfFactory = idp.getItpfFactory();

            final Itpf filteredPrecondition;
            if (!remainingApplications.isNoOp()) {
                filteredPrecondition = this.filterPrecondition(itpfFactory, implication.getPrecondition(), conclusionVariables);
                if (filteredPrecondition != implication.getPrecondition()) {
                    remainingApplications = remainingApplications.decreaseOneStep();
                    usedApplications = usedApplications.increaseOneStep();
                    totalImplication = totalImplication.mult(ImplicationType.COMPLETE);
                }
            } else {
                filteredPrecondition = implication.getPrecondition();
            }

            if (!usedApplications.isNoOp()) {
                return this.getSingletonReturn(
                    itpfFactory,
                    ItpfFactory.EMPTY_QUANTORS,
                    itpfFactory.createImplication(
                        filteredPrecondition,
                        itpfFactory.createAnd(processedConclusion.asCollection())), positive, totalImplication, usedApplications, false);
            } else {
                return null;
            }
        }

        return null;
    }

    private Itpf filterPrecondition(final ItpfFactory itpfFactory,
        final Itpf precondition,
        final Set<IVariable<?>> conclusionVariables) {
        final Set<ItpfConjClause> newClauses = new LinkedHashSet<ItpfConjClause>();
        boolean changed = false;
        for (final ItpfConjClause clause : precondition.getClauses()) {
            boolean changedClause = false;
            final Map<ItpfAtom, Boolean> newLiterals = new LinkedHashMap<ItpfAtom, Boolean>();
            for (final Map.Entry<ItpfAtom, Boolean> literal : clause.getLiterals().entrySet()) {
                if (literal.getKey().isBoolPolyVar() || conclusionVariables.containsAll(literal.getKey().getVariables())) {
                    newLiterals.put(literal.getKey(), literal.getValue());
                } else {
                    changedClause = true;
                }
            }

            if (changedClause) {
                newClauses.add(itpfFactory.createClause(ImmutableCreator.create(newLiterals), clause.getS()));
                changed = true;
            } else {
                newClauses.add(clause);
            }
        }

        if (changed) {
            return itpfFactory.create(precondition.getQuantification(),
                ImmutableCreator.create(newClauses));
        } else {
            return precondition;
        }
    }

    @Override
    protected ExecutionResult<? extends QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
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
