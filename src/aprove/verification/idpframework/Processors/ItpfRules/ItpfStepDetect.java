package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;

/**
 * @author mpluecke
 */
public class ItpfStepDetect extends ContextFreeItpfReplaceRule {

    public ItpfStepDetect() {
        super(new ExportableString("ItpfStepDetect"), new ExportableString(
            "ItpfStepDetect"));
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
        return CompatibleMarkClasses.I_STEP_DETECT.isCompatible(mark);
    }

    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive, final ImplicationType executionRequirements,
        final ApplicationMode mode, final Abortion aborter) {
        if (atom.isItp()) {
            final ItpfItp itp = (ItpfItp) atom;
            if (itp.getRelation() == ItpRelation.TO_TRANS) {
                if (!this.canUnify(idp, itp.getL(), itp.getR(), s)) {
                    final ItpfItp newItp =
                        idp.getIdpGraph().getItpfFactory().createItp(
                            itp.getL(), itp.getKLeft(),
                            itp.getContextL(), ItpRelation.TO_PLUS, itp.getR(),
                            itp.getKRight(), itp.getContextR());

                    return this.getSingletonReturn(idp.getItpfFactory(), newItp, positive, ImplicationType.EQUIVALENT, ApplicationMode.SingleStep, Boolean.FALSE);
                }
            }
        }
        return null;
    }

    private boolean canUnify(final IDPProblem idp,
        final ITerm<?> l,
        final ITerm<?> r,
        final Set<ITerm<?>> s) {
        if (s.contains(r)) {
            final ISubstitution mgu = l.getMGU(r);

            if (mgu == null) {
                return false;
            }
            final ITerm<?> unified = l.applySubstitution(mgu);

            final IQTermSet q = idp.getIdpGraph().getQ();

            if (!unified.isVariable()) {
                final IFunctionApplication<?> faUnified = (IFunctionApplication<?>) unified;
                return !q.canBeRewritten(faUnified);
            } else {
                return true;
            }
        } else {
            return l.unifies(r);
        }
    }

}
