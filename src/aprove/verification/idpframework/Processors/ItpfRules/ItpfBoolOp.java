package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Algorithms.UsableRules.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import immutables.*;

/**
 * @author mpluecke
 */
public class ItpfBoolOp extends ContextFreeItpfReplaceRule {

    public ItpfBoolOp() {
        super(new ExportableString("[i] BoolOp"), new ExportableString(
            "[i] BoolOp"));
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
        return CompatibleMarkClasses.I_BOOL_OP.isCompatible(mark);
    }

    @Override
    public boolean isSound() {
        return true;
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
            if (!itp.getL().isVariable()) {
                final IFunctionApplication<?> faL =
                    (IFunctionApplication<?>) itp.getL();
                boolean rValue;
                if (IDPPredefinedMap.isBooleanTrue(itp.getR())) {
                    rValue = true;
                } else if (IDPPredefinedMap.isBooleanFalse(itp.getR())) {
                    rValue = false;
                } else {
                    return null;
                }
                final boolean totalValue = positive ? rValue : !rValue;
                final PredefinedSemantics<?> sem =
                    faL.getRootSymbol().getSemantics();
                if (sem != null && !sem.isConstructor()) {
                    final PredefinedFunction<?, ?> func =
                        (PredefinedFunction<?, ?>) sem;
                    final IDPPredefinedMap predefinedMap =
                        idp.getPredefinedMap();
                    final ItpfFactory itpfFactory =
                        idp.getIdpGraph().getItpfFactory();
                    switch (func.getFunc()) {
                    case Lnot:
                        return this.processNot(predefinedMap, itpfFactory, itp, s,
                            !totalValue);
                    case Land:
                        if (!totalValue) {
                            return this.processOr(predefinedMap, itpfFactory, itp,
                                s, false);
                        } else {
                            return this.processAnd(predefinedMap, itpfFactory, itp,
                                s, true);
                        }
                    case Lor:
                        if (!totalValue) {
                            return this.processAnd(predefinedMap, itpfFactory, itp,
                                s, false);
                        } else {
                            return this.processOr(predefinedMap, itpfFactory, itp,
                                s, true);
                        }
                    default:
                    }
                }
            }
        }
        return null;
    }

    private ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processNot(final IDPPredefinedMap predefinedMap,
        final ItpfFactory itpfFactory,
        final ItpfItp itp,
        final Set<ITerm<?>> s,
        final boolean totalValue) {
        final IFunctionApplication<?> faL = (IFunctionApplication<?>) itp.getL();
        final ItpfItp newItp =
            itpfFactory.createItp(
                faL.getArgument(0),
                itp.getKLeft(),
                this.getContext(itp, faL.getRootSymbol(), 0, itp.canIgnoreContextL()),
                ItpRelation.TO_TRANS, predefinedMap.getBooleanTrue().getTerm(),
                itp.getKRight(), itp.getContextR());
        return this.getSingletonReturn(itpfFactory, newItp,
            totalValue, ImplicationType.EQUIVALENT,
            ApplicationMode.SingleStep, Boolean.TRUE);
    }

    private ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processOr(final IDPPredefinedMap predefinedMap,
        final ItpfFactory itpfFactory,
        final ItpfItp itp,
        final Set<ITerm<?>> s,
        final boolean value) {
        final IFunctionApplication<?> faL = (IFunctionApplication<?>) itp.getL();
        final ItpfItp newItpL =
            itpfFactory.createItp(
                faL.getArgument(0),
                itp.getKLeft(),
                this.getContext(itp, faL.getRootSymbol(), 0, itp.canIgnoreContextL()),
                ItpRelation.TO_TRANS, predefinedMap.getBooleanTrue().getTerm(),
                itp.getKRight(), itp.getContextR());
        final ItpfItp newItpR =
            itpfFactory.createItp(
                faL.getArgument(1),
                itp.getKLeft(),
                this.getContext(itp, faL.getRootSymbol(), 1, itp.canIgnoreContextL()),
                ItpRelation.TO_TRANS, predefinedMap.getBooleanTrue().getTerm(),
                itp.getKRight(), itp.getContextR());

        final Set<ItpfAtomReplaceData> or =
            new LinkedHashSet<ItpfAtomReplaceData>();
        or.add(new ItpfAtomReplaceData.LiteralMapData(new LiteralMap(newItpL, value), ITerm.EMPTY_SET));
        or.add(new ItpfAtomReplaceData.LiteralMapData(new LiteralMap(newItpR, value), ITerm.EMPTY_SET));

        return new ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData>(
            new QuantifiedDisjunction<ItpfAtomReplaceData>(ItpfFactory.EMPTY_QUANTORS, ImmutableCreator.create(or)),
            ImplicationType.EQUIVALENT, ApplicationMode.SingleStep, false);
    }

    private ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processAnd(final IDPPredefinedMap predefinedMap,
        final ItpfFactory itpfFactory,
        final ItpfItp itp,
        final Set<ITerm<?>> s,
        final boolean value) {
        final IFunctionApplication<?> faL = (IFunctionApplication<?>) itp.getL();
        final ItpfItp newItpL =
            itpfFactory.createItp(
                faL.getArgument(0),
                itp.getKLeft(),
                this.getContext(itp, faL.getRootSymbol(), 0, itp.canIgnoreContextL()),
                ItpRelation.TO_TRANS, predefinedMap.getBooleanTrue().getTerm(),
                itp.getKRight(), itp.getContextR());
        final ItpfItp newItpR =
            itpfFactory.createItp(
                faL.getArgument(1),
                itp.getKLeft(),
                this.getContext(itp, faL.getRootSymbol(), 1, itp.canIgnoreContextL()),
                ItpRelation.TO_TRANS, predefinedMap.getBooleanTrue().getTerm(),
                itp.getKRight(), itp.getContextR());
        return this.getAndReturn(itpfFactory, ItpfFactory.EMPTY_QUANTORS, value,
            ImplicationType.EQUIVALENT, ApplicationMode.SingleStep, Boolean.TRUE, newItpL, newItpR);
    }

    private IActiveContext getContext(final ItpfItp itp,
        final IFunctionSymbol<?> fs,
        final Integer pos,
        final boolean ignorable) {
        if (itp.getKLeft() != null) {
            if (ignorable) {
                return ItpfItp.EMPTY_CONTEXT;
            } else {
                return itp.getContextL().add(IActiveAtom.create(fs, pos));
            }
        } else {
            return null;
        }
    }

}