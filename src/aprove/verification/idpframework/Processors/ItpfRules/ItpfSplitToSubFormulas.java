package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class ItpfSplitToSubFormulas extends IDPExportable.IDPExportableSkeleton implements GenericItpfRule<Unused>, Mark<Unused> {

    @Override
    public Collection<? extends Mark<?>> getUsedMarks() {
        return Collections.<Mark<?>>singleton(this);
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
    public boolean isComplete() {
        return true;
    }

    @Override
    public boolean isSound() {
        return true;
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
        return mark.getClass().equals(this.getClass());
    }

    @Override
    public ExecutionResult<Conjunction<Itpf>, Itpf> process(final IDPProblem idp,
        final Itpf formula,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException {

        if (formula.getClauses().size() == 1) {
            final ItpfConjClause clause = formula.getClauses().iterator().next();

            if (clause.getLiterals().size() > 1) {
                final Set<Itpf> result = new LinkedHashSet<Itpf>();
                final ItpfFactory itpfFactory = idp.getItpfFactory();

                for (final Map.Entry<? extends ItpfAtom, Boolean> literal : clause.getLiterals().entrySet()) {
                    final Itpf singletonFormula = itpfFactory.create(formula.getQuantification(), itpfFactory.createClause(ImmutableCreator.create(Collections.<ItpfAtom, Boolean> singletonMap(literal.getKey(), literal.getValue())), clause.getS()));
                    result.add(singletonFormula);
                }

                return new ExecutionResult<Conjunction<Itpf>, Itpf>(
                    new Conjunction<Itpf>(ImmutableCreator.create(result)),
                    ImplicationType.EQUIVALENT,
                    ApplicationMode.SingleStep,
                    true
                    );
            }
        }

        return new ExecutionResult<Conjunction<Itpf>, Itpf>(
                new Conjunction<Itpf>(formula),
                ImplicationType.EQUIVALENT,
                ApplicationMode.NoOp,
                true
                );
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        sb.append("ItpfSplitToSubFormulas");
    }

}
