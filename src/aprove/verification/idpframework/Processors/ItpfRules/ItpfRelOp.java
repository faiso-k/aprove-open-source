package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;

/**
 * @author mpluecke
 */
public class ItpfRelOp extends ContextFreeItpfReplaceRule {

    public ItpfRelOp() {
        super(new ExportableString("ItpfRelOp"), new ExportableString(
            "ItpfRelOp"));
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
        return true;
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
        final Boolean positive, final ImplicationType executionRequirements, final ApplicationMode mode, final Abortion aborter) {
        if (atom.isItp()) {
            final ItpfItp itp = (ItpfItp) atom;
            if (!itp.getL().isVariable()) {
                final IFunctionApplication<?> faL =
                    (IFunctionApplication<?>) itp.getL();
                final PredefinedSemantics sem =
                    faL.getRootSymbol().getSemantics();
                if (sem != null && !sem.isConstructor()) {
                    final PredefinedFunction<?, ?> func =
                        (PredefinedFunction<?, ?>) sem;
                    final IDPPredefinedMap predefinedMap =
                        idp.getPredefinedMap();
                    boolean eq;
                    boolean swap;
                    switch (func.getFunc()) {
                    case Ge:
                        eq = true;
                        swap = false;
                        break;
                    case Gt:
                        eq = false;
                        swap = false;
                        break;
                    case Le:
                        eq = true;
                        swap = true;
                        break;
                    case Lt:
                        eq = false;
                        swap = true;
                        break;
                    default:
                        return null;
                    }
                    boolean totalValue = positive;
                    if (IDPPredefinedMap.isBooleanTrue(itp.getR())) {
                    } else if (IDPPredefinedMap.isBooleanFalse(itp.getR())) {
                        totalValue = !totalValue;
                    } else {
                        return null;
                    }
                    if (!totalValue) {
                        eq = !eq;
                        swap = !swap;
                    }
                    if (swap || !totalValue) {
                        final IFunctionSymbol<?> newFs;
                        if (eq) {
                            newFs =
                                predefinedMap.getFunctionSymbol(Func.Ge,
                                    sem.getDomains());
                        } else {
                            newFs =
                                predefinedMap.getFunctionSymbol(Func.Gt,
                                    sem.getDomains());
                        }
                        final IFunctionApplication<?> newFa;
                        if (swap) {
                            newFa =
                                ITerm.createFunctionApplication(
                                    newFs, faL.getArgument(1),
                                    faL.getArgument(0));
                        } else {
                            newFa =
                                ITerm.createFunctionApplication(
                                    newFs, faL.getArguments());
                        }

                        final ItpfItp newTp =
                            idp.getIdpGraph().getItpfFactory().createItp(newFa,
                                itp.getKLeft(), itp.getContextL(),
                                itp.getRelation(),
                                predefinedMap.getBooleanTrue().getTerm(),
                                itp.getKRight(), itp.getContextR());
                        return this.getSingletonReturn(idp.getItpfFactory(), newTp,
                            true,
                            ImplicationType.EQUIVALENT, ApplicationMode.SingleStep, false);
                    }
                }
            }
        }
        return null;
    }
}