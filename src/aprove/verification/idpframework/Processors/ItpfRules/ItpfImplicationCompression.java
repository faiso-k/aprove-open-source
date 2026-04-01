package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author MP
 */
public class ItpfImplicationCompression extends GenericItpfRule.GenericItpfRuleSkeleton<Unused> implements
        Mark<Unused> {

    public ItpfImplicationCompression() {
        super(new ExportableString("[i] ImplicationCompression"), new ExportableString("[i] ImplicationCompression"));
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
        return true;
    }

    @Override
    public Collection<? extends Mark<?>> getUsedMarks() {
        return Collections.<Mark<?>> singleton(this);
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
        return false;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return this.equals(mark);
    }

    @Override
    protected ExecutionResult<Conjunction<Itpf>, Itpf> process(final IDPProblem idp,
        final ItpfAndWrapper precondition,
        final Itpf formula,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException {

        final ItpfFactory itpfFactory = idp.getItpfFactory();

        final ApplicationMode remainingApplications = mode;
        final ApplicationMode usedApplications = ApplicationMode.NoOp;
        // FIXME: this is not done properly
        final boolean fixpointReached = false;

        final Set<ItpfConjClause> newClauses =
            new LinkedHashSet<ItpfConjClause>();
        boolean changedFormula = false;
        for (final ItpfConjClause clause : formula.getClauses()) {
            boolean changedClause = false;
            final LiteralMap newLiterals = new LiteralMap();

            if (remainingApplications != ApplicationMode.NoOp) {
                for (final Map.Entry<? extends ItpfAtom, Boolean> literal : clause.getLiterals().entrySet()) {
                    if (literal.getKey().isImplication() && remainingApplications != ApplicationMode.NoOp) {
                        final Pair<ItpfImplication, ApplicationMode> compressedImplication =
                            this.compressImplication(idp, precondition, (ItpfImplication) literal.getKey(),
                                executionRequirements, remainingApplications, aborter);

                        newLiterals.put(compressedImplication.x, literal.getValue());

                        remainingApplications.decreaseBy(compressedImplication.y);
                        usedApplications.increaseBy(compressedImplication.y);

                        changedClause =
                            changedClause
                                || compressedImplication.x != literal.getKey();
                    } else {
                        newLiterals.put(literal.getKey(), literal.getValue());
                    }
                }
            }
            if (changedClause) {
                newClauses.add(itpfFactory.createClause(
                    ImmutableCreator.create(newLiterals), clause.getS()));
                changedFormula = true;
            } else {
                newClauses.add(clause);
            }
        }

        final ExecutionResult<Conjunction<Itpf>, Itpf> result;

        if (changedFormula) {
            result = new ExecutionResult<Conjunction<Itpf>, Itpf>(
                    new Conjunction<Itpf>(itpfFactory.create(formula.getQuantification(),
                        ImmutableCreator.create(newClauses))),
                    ImplicationType.EQUIVALENT,
                    usedApplications, fixpointReached);

        } else {
            result = new ExecutionResult<Conjunction<Itpf>, Itpf>(
                    new Conjunction<Itpf>(formula),
                    ImplicationType.EQUIVALENT,
                    ApplicationMode.NoOp, fixpointReached);
        }

        return result;
    }

    private Pair<ItpfImplication, ApplicationMode> compressImplication(final IDPProblem idp,
        final ItpfAndWrapper precondition,
        final ItpfImplication implication,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException {
        Itpf newPrecondition = implication.getPrecondition();

        final ExecutionResult<Conjunction<Itpf>, Itpf> compressedConclusion =
            this.process(idp, precondition, implication.getConclusion(),
                executionRequirements, mode, aborter);

        Itpf newConclusion = compressedConclusion.iterator().next();

        final ApplicationMode remainingApplications = mode.decreaseBy(compressedConclusion.usedApplications);

        if (remainingApplications != ApplicationMode.NoOp &&
                newConclusion.getClauses().size() == 1) {
            final ItpfConjClause clause =
                newConclusion.getClauses().iterator().next();

            if (clause.getLiterals().size() == 1) {
                final Map.Entry<? extends ItpfAtom, Boolean> literal =
                    clause.getLiterals().entrySet().iterator().next();

                if (literal.getValue().booleanValue()
                    && literal.getKey().isImplication()) {
                    final ItpfImplication conclusionImplication =
                        (ItpfImplication) literal.getKey();
                    newPrecondition =
                        idp.getItpfFactory().createAnd(newPrecondition,
                            conclusionImplication.getPrecondition());
                    newConclusion = conclusionImplication.getConclusion();

                    return new Pair<ItpfImplication, ApplicationMode>(
                            idp.getItpfFactory().createImplication(
                                newPrecondition, newConclusion),
                            compressedConclusion.usedApplications.increaseBy(ApplicationMode.SingleStep)
                            );

                }
            }
        }

        if (newConclusion == implication.getConclusion()) {
            return new Pair<ItpfImplication, ApplicationMode>(
                    implication,
                    ApplicationMode.NoOp
                    );
        } else {
            return new Pair<ItpfImplication, ApplicationMode>(
                    idp.getItpfFactory().createImplication(
                        implication.getPrecondition(), newConclusion),
                    compressedConclusion.usedApplications
                    );
        }
    }

}
