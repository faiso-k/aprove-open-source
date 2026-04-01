package aprove.verification.idpframework.Processors.Filters;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Algorithms.UsableRules.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Martin Pluecker
 */
public class DupplicateArgsFilter extends AbstractIDPFilter<Result, TIDPProblem> {

    public DupplicateArgsFilter() {
        super("DupplicateArgsFilter", FilterMode.REMOVE_FILTERED_ATOMS);
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
        final Map<IFunctionSymbol<?>, List<List<IActiveAtom>>> equivalentPositions =
            new LinkedHashMap<IFunctionSymbol<?>, List<List<IActiveAtom>>>();

        this.initializeEquivalentPositions(idp, equivalentPositions, aborter);

        this.splitEquivalenceClasses(idp.getIdpGraph().getTerms(), equivalentPositions, aborter);
        this.splitEquivalenceClassesbyFormula(idp.getIdpGraph().getEdgeConditions().values(), equivalentPositions, aborter);
        this.splitEquivalenceClassesbyFormula(idp.getIdpGraph().getNodeConditions().values(), equivalentPositions, aborter);

        final FilterReplacement filter =
            this.createFilter(idp, equivalentPositions, aborter);

        final IDPProblem newIDP =
            this.createNewIDP(idp, filter, aborter);

        if (newIDP != idp) {
            return ResultFactory.proved(newIDP, YNMImplication.EQUIVALENT,
                new DupplicateArgsFilterProof(filter));
        }
        return ResultFactory.unsuccessful();
    }

    private void initializeEquivalentPositions(final IDPProblem idp,
        final Map<IFunctionSymbol<?>, List<List<IActiveAtom>>> equivalentPositions,
        final Abortion aborter) {
        for (final IFunctionSymbol<?> fs : idp.getIdpGraph().getFunctionSymbols()) {
            final List<IActiveAtom> positions = new ArrayList<IActiveAtom>(fs.getArity());
            for (int i = fs.getArity() - 1; i >= 0 ; i--) {
                positions.add(IActiveAtom.create(fs, i));
            }

            equivalentPositions.put(fs, Collections.singletonList(positions));
        }
    }

    private void splitEquivalenceClassesbyFormula(final Collection<Itpf> formulas,
        final Map<IFunctionSymbol<?>, List<List<IActiveAtom>>> equivalentPositions,
        final Abortion aborter) throws AbortionException {
        for (final Itpf formula : formulas) {
            this.splitEquivalenceClasses(formula.getTerms(true),
                equivalentPositions,
                aborter);
        }
    }

    private void splitEquivalenceClasses(final Collection<? extends ITerm<?>> terms,
        final Map<IFunctionSymbol<?>, List<List<IActiveAtom>>> equivalentPositions,
        final Abortion aborter) throws AbortionException {
        for (final ITerm<?> term : terms) {
            if (!term.isVariable()) {
                this.splitEquivalenceClasses((IFunctionApplication<?>) term, equivalentPositions, aborter);
                aborter.checkAbortion();
            }
        }
    }

    private void splitEquivalenceClasses(final IFunctionApplication<?> fa,
        final Map<IFunctionSymbol<?>, List<List<IActiveAtom>>> equivalentPositions,
        final Abortion aborter) throws AbortionException {
        final IFunctionSymbol<?> rootFs = fa.getRootSymbol();
        final List<List<IActiveAtom>> eqClasses = equivalentPositions.remove(rootFs);
        if (eqClasses != null) {
            final List<List<IActiveAtom>> newEqClasses = new ArrayList<List<IActiveAtom>>();
            for (final List<IActiveAtom> eqClass : eqClasses) {
                final CollectionMap<ITerm<?>, IActiveAtom> split = new CollectionMap<ITerm<?>, IActiveAtom>(CollectionCreator.arrayList());

                for (final IActiveAtom pos : eqClass) {
                    split.add(fa.getArgument(pos.pos), pos);
                }

                for (final Collection<IActiveAtom> newClass : split.values()) {
                    if (newClass.size() > 1) {
                        newEqClasses.add((List<IActiveAtom>) newClass);
                    }
                }
            }

            if (!newEqClasses.isEmpty()) {
                equivalentPositions.put(rootFs, newEqClasses);
            }

            aborter.checkAbortion();
        }

        this.splitEquivalenceClasses(fa.getArguments(), equivalentPositions, aborter);
    }

    private FilterReplacement createFilter(final IDPProblem idp, final Map<IFunctionSymbol<?>, List<List<IActiveAtom>>> equivalentPositions,
        final Abortion aborter) throws AbortionException {
        final Map<IFunctionSymbol<?>, List<Boolean>> retainedPositions = new LinkedHashMap<IFunctionSymbol<?>, List<Boolean>>();

        for (final Map.Entry<IFunctionSymbol<?>, List<List<IActiveAtom>>> fsEqClasses: equivalentPositions.entrySet()) {
            final IFunctionSymbol<?> fs = fsEqClasses.getKey();
            final List<Boolean> fsRetainedPositions = new ArrayList<Boolean>(fs.getArity());
            for (int i = fs.getArity() - 1; i >= 0; i--) {
                fsRetainedPositions.add(Boolean.TRUE);
            }

            for (final List<IActiveAtom> fsEqPositions : fsEqClasses.getValue()) {
                final Iterator<IActiveAtom> iterator = fsEqPositions.iterator();

                // retained
                iterator.next();
                while(iterator.hasNext()) {
                    fsRetainedPositions.set(iterator.next().pos, Boolean.FALSE);
                }
            }

            retainedPositions.put(fsEqClasses.getKey(), fsRetainedPositions);
        }

        final FunctionSymbolReplacement fsReplacement = this.createFsReplaceMap(idp, retainedPositions, aborter);

        return new FilterReplacement(fsReplacement, VarRenaming.EMPTY_RENAMING);
    }

    public static class DupplicateArgsFilterProof extends AbstractFilterProof {

        public DupplicateArgsFilterProof(final FilterReplacement filter) {
            super(filter);
        }

    }
}