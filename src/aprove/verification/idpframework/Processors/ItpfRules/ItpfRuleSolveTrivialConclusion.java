package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.idpframework.Processors.ItpfRules.ItpfAtomReplaceData.*;
import immutables.*;

/**
 * Removes trivial conclusions of the type Phi & Psi ==> Phi & Gamma ist transformed to Phi & Psi ==> Gamma
 * @author MP
 */
public class ItpfRuleSolveTrivialConclusion extends ContextFreeItpfReplaceRule {

    public ItpfRuleSolveTrivialConclusion() {
        super(new ExportableString("[i] SolveTrivialConclusion"), new ExportableString("[i] SolveTrivialConclusion"));
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
        return CompatibleMarkClasses.SOLVE_TRIVIAL_CONCLUSION.isCompatible(mark);
    }

    @Override
    protected ExecutionResult<? extends QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
        final aprove.verification.idpframework.Processors.ItpfRules.ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException {
        for (final ItpfConjClause preconditionClause : precondition.getFormula().getClauses()) {
            final Boolean atomPrecondValue = preconditionClause.getLiterals().get(atom);
            if (atomPrecondValue == null) {
                return null;
            }

            if (!atomPrecondValue.equals(positive)) {
                return null;
            }

            if (!preconditionClause.getS().containsAll(s)) {
                return null;
            }
        }
        return this.getEmptyReturn(idp.getItpfFactory(), ImplicationType.EQUIVALENT, ApplicationMode.SingleStep);
    }

    @Override
    protected ItpfAtomReplaceData createReplaceData(final ItpfFactory itpfFactory,
        final LiteralMap conjunction,
        final ImmutableSet<ITerm<?>> sTerms) {
        return new LiteralMapData(conjunction, sTerms);
    }

}
