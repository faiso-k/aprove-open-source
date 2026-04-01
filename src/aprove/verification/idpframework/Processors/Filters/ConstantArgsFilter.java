package aprove.verification.idpframework.Processors.Filters;

import java.util.*;
import java.util.Map.Entry;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.oldframework.Logic.*;

/**
 * @author Martin Pluecker
 */
public class ConstantArgsFilter extends AbstractIDPFilter<Result, TIDPProblem> {

    public ConstantArgsFilter() {
        super("ConstantArgsFilter", FilterMode.REMOVE_FILTERED_ATOMS);
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return false;
    }

    @Override
    public boolean isIDPApplicable(final IDPProblem idp) {
        return true;
    }

    @Override
    protected Result processIDPProblem(final TIDPProblem idp,
        final Abortion aborter) throws AbortionException {
        final Map<IFunctionSymbol<?>, List<ITerm<?>>> constantArgs =
            new LinkedHashMap<IFunctionSymbol<?>, List<ITerm<?>>>();

        this.findConstantArgs(idp.getIdpGraph().getTerms(), constantArgs, aborter);
        this.findConstantArgsInFormulas(idp.getIdpGraph().getEdgeConditions().values(), constantArgs, aborter);
        this.findConstantArgsInFormulas(idp.getIdpGraph().getNodeConditions().values(), constantArgs, aborter);

        final FilterReplacement filter =
            this.createFilter(idp, constantArgs, aborter);

        final IDPProblem newIDP =
            this.createNewIDP(idp, filter, aborter);

        if (newIDP != idp) {
            return ResultFactory.proved(newIDP, YNMImplication.EQUIVALENT,
                new ConstantArgsFilterProof(filter));
        }
        return ResultFactory.unsuccessful();
    }

    private void findConstantArgsInFormulas(final Collection<Itpf> formulas,
        final Map<IFunctionSymbol<?>, List<ITerm<?>>> constantArgs,
        final Abortion aborter) throws AbortionException {
        for (final Itpf formula : formulas) {
            this.findConstantArgs(formula.getTerms(true),
                constantArgs,
                aborter);
        }
    }

    private void findConstantArgs(final Collection<? extends ITerm<?>> terms,
        final Map<IFunctionSymbol<?>, List<ITerm<?>>> constantArgs,
        final Abortion aborter) throws AbortionException {
        for (final ITerm<?> term : terms) {
            if (!term.isVariable()) {
                this.findConstantArgs((IFunctionApplication<?>) term, constantArgs, aborter);
                aborter.checkAbortion();
            }
        }
    }

    private void findConstantArgs(final IFunctionApplication<?> fa,
        final Map<IFunctionSymbol<?>, List<ITerm<?>>> constantArgs,
        final Abortion aborter) throws AbortionException {
        final IFunctionSymbol<?> rootFs = fa.getRootSymbol();
        final List<ITerm<?>> fsConstantArgs = constantArgs.get(rootFs);
        if (fsConstantArgs != null) {
            for (int i = rootFs.getArity() - 1; i >= 0; i--) {
                if (!fa.getArgument(i).equals(fsConstantArgs.get(i))) {
                    fsConstantArgs.set(i, null);
                }
            }
        } else {
            constantArgs.put(rootFs, new ArrayList<ITerm<?>>(fa.getArguments()));
        }

        this.findConstantArgs(fa.getArguments(), constantArgs, aborter);
    }

    private FilterReplacement createFilter(final IDPProblem idp, final Map<IFunctionSymbol<?>, List<ITerm<?>>> constantArgs,
        final Abortion aborter) throws AbortionException {
        final Map<IFunctionSymbol<?>, List<Boolean>> retainedPositions = new LinkedHashMap<IFunctionSymbol<?>, List<Boolean>>();

        for (final Entry<IFunctionSymbol<?>, List<ITerm<?>>> fsConstantArgs: constantArgs.entrySet()) {
            final IFunctionSymbol<?> fs = fsConstantArgs.getKey();
            final List<Boolean> fsRetainedPositions = new ArrayList<Boolean>(fs.getArity());
            for (final ITerm<?> constantArg : fsConstantArgs.getValue()) {
                if (constantArg != null && constantArg.isGroundTerm()) {
                    fsRetainedPositions.add(Boolean.FALSE);
                } else {
                    fsRetainedPositions.add(Boolean.TRUE);
                }
            }
            retainedPositions.put(fs, fsRetainedPositions);
        }

        final FunctionSymbolReplacement fsReplacement = this.createFsReplaceMap(idp, retainedPositions, aborter);

        return new FilterReplacement(fsReplacement, VarRenaming.EMPTY_RENAMING);
    }

    public static class ConstantArgsFilterProof extends AbstractFilterProof {

        public ConstantArgsFilterProof(final FilterReplacement filter) {
            super(filter);
        }

    }
}