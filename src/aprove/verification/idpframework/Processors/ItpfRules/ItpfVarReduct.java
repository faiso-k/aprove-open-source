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

/**
 *
 * @author mpluecke
 */
public class ItpfVarReduct extends ContextFreeItpfReplaceRule {

    public ItpfVarReduct() {
        super(new ExportableString("[i] VarReduct"), new ExportableString(
            "[i] VarReduct"));
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
        final Boolean positive, final ImplicationType executionRequirements,
        final ApplicationMode mode, final Abortion aborter) {
        if (atom.isItp()) {
            final ItpfItp tp = (ItpfItp) atom;
            if (tp.getRelation() == ItpRelation.TO_TRANS) {
                final ITerm<?> l = tp.getL();
                final Set<IVariable<?>> sVars = CollectionUtil.getVariables(s);

                if (!sVars.containsAll(l.getVariables())) {
                    return null;
                }

                final Set<IFunctionSymbol<?>> definedSymbols =
                    idp.getIdpGraph().getDefinedSymbols();

                for (final IFunctionSymbol<?> fs : l.getFunctionSymbols()) {
                    if ((fs.getSemantics() != null && !fs.getSemantics().isConstructor())
                        || definedSymbols.contains(fs)) {
                        return null;
                    }
                }

                final ItpfFactory itpfFactory = idp.getItpfFactory();

                final ITerm<?> r = tp.getR();
                final ItpfItp newTp =
                    itpfFactory.createItp(l,
                        tp.getKLeft(), tp.getContextL(),
                        ItpRelation.EQ, r, tp.getKRight(), tp.getContextR());

                return this.getSingletonReturn(itpfFactory, newTp, positive, ImplicationType.EQUIVALENT, ApplicationMode.SingleStep, false);
            } else if (tp.getRelation() == ItpRelation.TO_PLUS || tp.getRelation() == ItpRelation.TO) {
                final ITerm<?> l = tp.getL();
                final Set<IVariable<?>> sVars =
                    CollectionUtil.getVariables(s);
                if (l.isVariable() && sVars.contains(l)) {
                    return this.getUnsatReturn(ImplicationType.EQUIVALENT, ApplicationMode.SingleStep);
                }
            }
        }
        return null;
    }


}
