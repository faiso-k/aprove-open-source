package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;

/**
 * @author MP
 */
public class ItpfDropPreconditions extends ContextFreeItpfReplaceRule {

    public ItpfDropPreconditions() {
        super(new ExportableString("ItpfDropPreconditions"), new ExportableString(
        "ItpfDropPreconditions"));
    }

    @Override
    public boolean isApplicable(final IDPProblem idp) {
        return idp.getIdpGraph().getPolyInterpretation() != null;
    }

    @Override
    public boolean isComplete() {
        return false;
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
        return true;
    }

    @Override
    public boolean isContextFree() {
        return true;
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

        if (executionRequirements.isComplete() || atom.isBoolPolyVar()) {
            return null;
        }

        if (atom.isPoly()) {
            final PolyInterpretation<?> polyInterpretation = idp.getPolyInterpretation();
            final ItpfPolyAtom<?> polyAtom = (ItpfPolyAtom<?>) atom;
            final Set<IVariable<?>> vars = new LinkedHashSet<IVariable<?>>();
            polyAtom.collectVariables(vars);

            boolean hasUniversalQuantifiedVariable = false;
            for (final IVariable<?> var : vars) {
                if (!polyInterpretation.isExistQuantified(var)) {
                    hasUniversalQuantifiedVariable = true;
                    break;
                }
            }

            if (!hasUniversalQuantifiedVariable) {
                return null;
            }
        }

        return this.getEmptyReturn(idp.getItpfFactory(), ImplicationType.SOUND, ApplicationMode.SingleStep);
    }

}
