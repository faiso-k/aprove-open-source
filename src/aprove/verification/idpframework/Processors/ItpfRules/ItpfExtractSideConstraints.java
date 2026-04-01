package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class ItpfExtractSideConstraints extends ContextFreeItpfReplaceRule {

    public ItpfExtractSideConstraints() {
        super(new ExportableString("ItpfExtractSideConstraints"), new ExportableString("ItpfExtractSideConstraints"));
    }

    @Override
    public boolean isApplicable(final IDPProblem idp) {
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
       return false;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return mark.getClass() == this.getClass();
    }

    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive, final ImplicationType executionRequirements,
        final ApplicationMode mode, final Abortion aborter) {
        final SideConstraintStore sideConstrains = idp.getIdpGraph().getSideConstraints();

        final ImplicationType requirement = positive ? executionRequirements : executionRequirements.invert();
        if (sideConstrains.hasReplacement(precondition.getFormula(), atom, requirement)) {

            final ImmutablePair<ItpfBoolPolyVar<?>, ImplicationType> replacement =
                sideConstrains.getReplacement(precondition.getFormula(), atom, requirement);

            return this.getSingletonReturn(idp.getItpfFactory(), replacement.x, positive, replacement.y, ApplicationMode.SingleStep, false);
        } else {
//            System.err.println("No side constraint for: " + atom);
            return null;
        }
    }


}
