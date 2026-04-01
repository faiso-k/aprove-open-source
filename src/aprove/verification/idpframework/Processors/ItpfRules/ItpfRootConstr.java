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

/**
 * @author mpluecke
 */
public class ItpfRootConstr extends ContextFreeItpfReplaceRule {

    public ItpfRootConstr() {
        super(new ExportableString("ItpfRootConstr"), new ExportableString(
            "ItpfRootConstr"));
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
        return CompatibleMarkClasses.I_ROOT_CONSTRUCTOR.isCompatible(mark);
    }

    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive, final ImplicationType executionRequirements,
        final ApplicationMode mode, final Abortion aborter){
        if (atom.isItp()) {
            final ItpfItp tp = (ItpfItp) atom;
            if (tp.getRelation() == ItpRelation.TO
                || tp.getRelation() == ItpRelation.TO_TRANS
                || tp.getRelation() == ItpRelation.TO_PLUS) {
                final ITerm<?> l = tp.getL();
                final ITerm<?> r = tp.getR();
                if (!l.isVariable() && !r.isVariable()) {
                    final IDPPredefinedMap predefinedMap =
                        idp.getPredefinedMap();
                    final IFunctionApplication<?> fl = (IFunctionApplication<?>) l;
                    if (fl.getRootSymbol().getSemantics() == null
                        && !idp.getIdpGraph().getDefinedSymbols().contains(
                            fl.getRootSymbol())) {
                        final IFunctionApplication<?> fr =
                            (IFunctionApplication<?>) r;
                        if (!fl.getRootSymbol().equals(fr.getRootSymbol())) {
                            // clash failure
                            return this.getUnsatReturn(ImplicationType.EQUIVALENT, ApplicationMode.SingleStep);
                        } else {
                            // reduce function symbol
                            final LiteralMap children = new LiteralMap();
                            final IFunctionSymbol<?> rootL = fl.getRootSymbol();
                            final int arity = rootL.getArity();
                            for (int i = 0; i < arity; i++) {
                                final IActiveContext contextL = tp.getContextL();

                                final IActiveContext contextR = tp.getContextR();

                                final ItpfItp newChild =
                                    idp.getIdpGraph().getItpfFactory().createItp(
                                        fl.getArgument(i), tp.getKLeft(),
                                        contextL, ItpRelation.TO_TRANS,
                                        fr.getArgument(i), tp.getKRight(),
                                        contextR);
                                children.put(newChild, positive);
                            }
                            return this.createReplaceData(idp.getItpfFactory(), ItpfFactory.EMPTY_QUANTORS, children, ImplicationType.EQUIVALENT, ApplicationMode.SingleStep, true);
                        }
                    }
                }
            }
        }
        return null;
    }
}
