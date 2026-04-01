package aprove.verification.idpframework.Processors.Filters;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Algorithms.UsableRules.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Processors.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author MP
 */
// FIXME : when node term is filtered, some variables in edge and node conditions may become free, corresponding variables should be quantified or atoms should be removed
public abstract class AbstractIDPFilter<ResultType extends Result, ProblemType extends IDPProblem> extends IDPProcessor<ResultType, ProblemType> {

    public static enum FilterMode {
        QUANTIFY_FILTERED_VARIABLES,
        REMOVE_FILTERED_ATOMS;
    }

    private final FilterMode filterMode;

    protected AbstractIDPFilter(final String description, final FilterMode filterMode) {
        super(description);
        this.filterMode = filterMode;
    }

    protected ProblemType createNewIDP(final ProblemType idp,
        final FilterReplacement filterReplacement,
        final Abortion aborter) throws AbortionException {

        this.assertSoundFilter(idp, filterReplacement, aborter);

        boolean changed = false;
        for (final Map.Entry<IFunctionSymbol<?>, ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>>> fsReplace : filterReplacement.functionSymbolReplacement.entrySet()) {
            if (!fsReplace.getKey().equals(fsReplace.getValue().x)) {
                changed = true;
                break;
            }
        }

        if (!changed) {
            changed = !filterReplacement.variableReplacement.isEmpty();
        }

        if (!changed) {
            return idp;
        }

        final Map<INode, ITerm<?>> newTerms =
            this.createNewTerms(idp, filterReplacement);

        final Map<INode, VarRenaming> newLoopRenamings =
            this.createNewLoopRenamings(idp, newTerms, filterReplacement);

        final IQTermSet newQ = this.createNewQ(idp, filterReplacement);

        final Map<IFunctionSymbol<?>, ImmutableSet<INode>> newInitialRewriteNodes =
            this.createNewInitialNodes(idp, filterReplacement);

        final Map<INode, Itpf> newNodeConditions =
            this.createNewNodeConditions(idp, newTerms, newLoopRenamings, filterReplacement, aborter);

        final Pair<Map<IEdge, IEdge>, Map<IEdge, Itpf>> newEdges =
            this.createNewEdges(idp, newTerms, newLoopRenamings, filterReplacement, aborter);


        final IDependencyGraph newIDPGraph = IDependencyGraph.create(
            idp.getPredefinedMap(),
            newQ,
            idp.getIdpGraph().getItpfFactory(),
            idp.getIdpGraph().getPolyInterpretation(),
            ImmutableCreator.create(newTerms),
            ImmutableCreator.create(newNodeConditions),
            ImmutableCreator.create(newInitialRewriteNodes),
            idp.getIdpGraph().getNodeUnrollCounter(),
            ImmutableCreator.create(newLoopRenamings),
            ImmutableCreator.create(newEdges.y),
            idp.getIdpGraph().getFreshVarGenerator());

        if (idp instanceof TIDPProblem) {
            final TIDPProblem tidp = (TIDPProblem) idp;
            final ImmutableSet<IDPSubGraph> newSubGraphs = this.createNewSubgraphs(tidp.getSubGraphs(), newEdges.x);

            return (ProblemType) tidp.change(
                newIDPGraph,
                newSubGraphs);
        } else {
            return (ProblemType) idp.change(newIDPGraph);
        }

    }

    private void assertSoundFilter(final IDPProblem idp,
        final FilterReplacement filterReplacement,
        final Abortion aborter) throws AbortionException {
        if (Globals.useAssertions) {
            final LinkedHashSet<IActiveAtom> activePositions = new LinkedHashSet<IActiveAtom>();

            final IDependencyGraph graph = idp.getIdpGraph();
            for (final IEdge edge : graph.getEdges()) {
                final ITerm<?> fromTerm = graph.getTerm(edge.from);
                activePositions.addAll(
                    IActiveContext.create(fromTerm, edge.fromPos).getContext());
            }

            aborter.checkAbortion();

            final FunctionSymbolReplacement fsReplacement = filterReplacement.functionSymbolReplacement;
            for (final IActiveAtom activeAtom : activePositions) {
                final ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>> replacement =
                    fsReplacement.get(activeAtom.fs);
                assert replacement == null || replacement.y.get(activeAtom.pos) : "positions with outgoing edges must not be filtered";
            }
        }
    }

    private void completeToSoundFilter(final IDPProblem idp,
        final Map<IFunctionSymbol<?>, ? extends List<Boolean>> retainedPositions,
        final Abortion aborter) throws AbortionException {
        final LinkedHashSet<IActiveAtom> activePositions = new LinkedHashSet<IActiveAtom>();

        final IDependencyGraph graph = idp.getIdpGraph();
        for (final IEdge edge : graph.getEdges()) {
            if (edge.type.isInf()) {
                final ITerm<?> fromTerm = graph.getTerm(edge.from);
                activePositions.addAll(
                    IActiveContext.create(fromTerm, edge.fromPos).getContext());
            }
        }

        aborter.checkAbortion();

        for (final IActiveAtom activeAtom : activePositions) {
            final List<Boolean> retained =
                retainedPositions.get(activeAtom.fs);
            if (retained != null) {
                retained.set(activeAtom.pos, Boolean.TRUE);
            }
        }
    }

    protected FunctionSymbolReplacement createFsReplaceMap(final IDPProblem idp,
        final Map<IFunctionSymbol<?>, ? extends List<Boolean>> retainedPositions, final Abortion aborter) throws AbortionException {
        final IDPPredefinedMap predefinedMap = idp.getPredefinedMap();
        this.completeToSoundFilter(idp, retainedPositions, aborter);

        final FunctionSymbolReplacement fsReplacementMap =
            new FunctionSymbolReplacement();

        for (final Map.Entry<IFunctionSymbol<?>, ? extends List<Boolean>> retainedPosition : retainedPositions.entrySet()) {
            final IFunctionSymbol<?> fs = retainedPosition.getKey();
            final List<Boolean> retainedArgs = retainedPosition.getValue();
            if (fs.getSemantics() == null) {
                int newArity = 0;
                for (int argIndex = 0; argIndex < fs.getArity(); argIndex ++) {
                   if (retainedArgs.get(argIndex)) {
                       newArity++;
                   }
                }

                if (newArity != fs.getArity()) {
                    final ArrayList<SemiRingDomain<?>> newDomains =
                        this.getNewDomains(fs, retainedArgs, newArity);

                    final IFunctionSymbol<?> newFs = IFunctionSymbol.create(fs.getName(),
                        ImmutableCreator.create(newDomains),
                        fs.getResultDomain(),
                        predefinedMap);

                    fsReplacementMap.put(fs, new ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>>(newFs,
                            ImmutableCreator.create(retainedArgs)));
//                } else {
//                    fsReplacementMap.put(fs,
//                        new ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>>(fs,
//                                ImmutableCreator.create(retainedArgs)));
                }
            }
        }
        return fsReplacementMap;
    }

    protected ArrayList<SemiRingDomain<?>> getNewDomains(final IFunctionSymbol<?> fs,
        final List<Boolean> retainedArgs,
        final int newArity) {
        final ArrayList<SemiRingDomain<?>> newDomains =
            new ArrayList<SemiRingDomain<?>>(newArity);
        final ImmutableList<? extends SemiRingDomain<?>> oldDomains =
            fs.getDomains();
        for (int argIndex = 0; argIndex < fs.getArity(); argIndex ++) {
            if (retainedArgs.get(argIndex)) {
                newDomains.add(oldDomains.get(argIndex));
            }
         }
        return newDomains;
    }

    protected Map<IFunctionSymbol<?>, ImmutableSet<INode>> createNewInitialNodes(final IDPProblem idp,
        final FilterReplacement filterReplacement) {
        final FunctionSymbolReplacement fsReplacement = filterReplacement.functionSymbolReplacement;

        final Map<IFunctionSymbol<?>, ImmutableSet<INode>> res = new LinkedHashMap<IFunctionSymbol<?>, ImmutableSet<INode>>();

        for (final Map.Entry<IFunctionSymbol<?>, ImmutableSet<INode>> initialNodes : idp.getIdpGraph().getInitialRewriteNodes().entrySet()) {
            final ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>> fsReplace =
                fsReplacement.get(initialNodes.getKey());
            IFunctionSymbol<?> newFs;

            if (fsReplace != null) {
                newFs = fsReplace.x;
            } else {
                newFs = null;
            }

            if (newFs == null) {
                newFs = initialNodes.getKey();
            }
            res.put(newFs, initialNodes.getValue());
        }

        return res;
    }

    protected Map<INode, VarRenaming> createNewLoopRenamings(final IDPProblem idp,
        final Map<INode, ITerm<?>> newTerms, final FilterReplacement filterReplacement) {

        final Map<INode, VarRenaming> newLoopRenamings =
            new LinkedHashMap<INode, VarRenaming>();

        final PolyFactory polyFactory = idp.getIdpGraph().getPolyFactory();

        for (final Map.Entry<INode, VarRenaming> renaming : idp.getIdpGraph().getLoopRenamings().entrySet()) {
            final VarRenaming varSubst = filterReplacement.variableReplacement;
            final ITerm<?> newTerm = newTerms.get(renaming.getKey());
            final Set<IVariable<?>> newTermVariables = newTerm.getVariables();

            final Map<IVariable<?>, IVariable<?>> newRenaming =
                new LinkedHashMap<IVariable<?>, IVariable<?>>();
            for (final Map.Entry<IVariable<?>, ? extends IVariable<?>> r : renaming.getValue().getMap().entrySet()) {
                final IVariable<?> newKey =
                    r.getKey().applyVarSubstitution(varSubst);
                if (newTermVariables.contains(newKey)) {
                    final IVariable<?> newValue;
                    if (newKey != r.getKey()) {
                        newValue =
                            ITerm.createVariable(
                                r.getValue().getName(), newKey.getDomain());
                    } else {
                        newValue = r.getValue();
                    }
                    newRenaming.put(newKey, newValue);
                }
            }

            newLoopRenamings.put(renaming.getKey(),
                VarRenaming.create(ImmutableCreator.create(newRenaming), true, polyFactory));
        }
        return newLoopRenamings;
    }

    protected Pair<Map<IEdge, IEdge>, Map<IEdge, Itpf>> createNewEdges(final IDPProblem idp,
        final Map<INode, ITerm<?>> newTerms,
        final Map<INode, VarRenaming> newLoopRenamings,
        final FilterReplacement filterReplacement, final Abortion aborter) throws AbortionException {
        final ItpfFactory itpfFactory = idp.getItpfFactory();
        final VarRenaming varSubst = filterReplacement.variableReplacement;

        final Map<IEdge, IEdge> edgeReplacement =
            new LinkedHashMap<IEdge, IEdge>();

        final Map<IEdge, Itpf> conditionReplacement =
            new LinkedHashMap<IEdge, Itpf>();

        final IDependencyGraph graph = idp.getIdpGraph();

        for (final Map.Entry<IEdge, Itpf> edgeCondition : graph.getEdgeConditions().entrySet()) {
            final IEdge edge = edgeCondition.getKey();

            final IPosition newEdgeFromPos = this.createNewFromPos(graph.getTerm(edge.from), edge.fromPos, filterReplacement);

            if (Globals.useAssertions) {
                assert !edge.type.isInf()
                    || newTerms.get(edge.from).isValidPosition(newEdgeFromPos) : "filtering at inf positions not allowed";
            }

            final Itpf condition = edgeCondition.getValue();

            Itpf replaced = condition.replaceAllFunctionSymbols(filterReplacement.functionSymbolReplacement);
            final Set<IVariable<?>> retainedVariables = new HashSet<IVariable<?>>();

            if (edge.from != edge.to) {
                replaced = replaced.applySubstitution(varSubst, true);
                newTerms.get(edge.from).collectVariables(retainedVariables);
                newTerms.get(edge.to).collectVariables(retainedVariables);
            } else {
                final INode fromNode = edge.from;
                final ITerm<?> oldTerm = idp.getIdpGraph().getTerm(fromNode);

                final VarRenaming oldLoopRenaming =
                    idp.getIdpGraph().getLoopRenamings().get(fromNode);
                final VarRenaming newLoopRenaming =
                    newLoopRenamings.get(fromNode);

                final Map<IVariable<?>, IVariable<?>> extendedVarSubst =
                    new LinkedHashMap<IVariable<?>, IVariable<?>>(
                        varSubst.getMap());

                for (final IVariable<?> oldVar : oldTerm.getVariables()) {
                    extendedVarSubst.put(
                        oldVar.applyVarSubstitution(oldLoopRenaming),
                        oldVar.applyVarSubstitution(oldLoopRenaming).applyVarSubstitution(varSubst));
                }

                final VarRenaming extendedVarSubtitution = VarRenaming.create(ImmutableCreator.create(extendedVarSubst), false, idp.getIdpGraph().getPolyFactory());

                replaced =
                    replaced.applySubstitution(extendedVarSubtitution);

                newTerms.get(edge.from).collectVariables(retainedVariables);
                newTerms.get(edge.to).applySubstitution(newLoopRenaming).collectVariables(retainedVariables);
            }

            final Itpf filteredReplace = this.filterCondition(idp, replaced, retainedVariables, itpfFactory, aborter);

            final IEdge newEdge = IEdge.create(edge.from, newEdgeFromPos, edge.to, edge.type);
            edgeReplacement.put(edge, newEdge );

            conditionReplacement.put(
                newEdge,
                filteredReplace);
        }
        return new Pair<Map<IEdge,IEdge>, Map<IEdge,Itpf>>(edgeReplacement, conditionReplacement);
    }

    private IPosition createNewFromPos(final ITerm<?> term,
        final IPosition fromPos,
        final FilterReplacement filterReplacement) {
        if (fromPos.isEmptyPosition()) {
            return fromPos;
        }

        final int[] newPos = new int[fromPos.getDepth()];

        IFunctionApplication<?> fa = (IFunctionApplication<?>) term;
        final int depth = fromPos.getDepth();
        for (int d = 0; d < depth; d++) {
            final int fromP = fromPos.getPosition(d);
            newPos[d] = filterReplacement.functionSymbolReplacement.getNewPosition(fa.getRootSymbol(), fromP);
            if (d < depth - 1) {
                fa = (IFunctionApplication<?>) fa.getArgument(fromP);
            }
        }

        return IPosition.create(newPos);
    }

    protected Map<INode, Itpf> createNewNodeConditions(final IDPProblem idp,
        final Map<INode, ITerm<?>> newTerms, final Map<INode, VarRenaming> newLoopRenamings, final FilterReplacement filterReplacement, final Abortion aborter) throws AbortionException {
        final Map<INode, Itpf> newConditions = new LinkedHashMap<INode, Itpf>();

        final ItpfFactory itpfFactory = idp.getItpfFactory();

        for (final Map.Entry<INode, Itpf> node : idp.getIdpGraph().getNodeConditions().entrySet()) {
            final VarRenaming varSubst = filterReplacement.variableReplacement;

            Itpf replaced =
                node.getValue().replaceAllFunctionSymbols(filterReplacement.functionSymbolReplacement);

            final Set<IVariable<?>> nodeVariables = newTerms.get(node.getKey()).getVariables();

            replaced = replaced.applySubstitution(varSubst, true);

            final Itpf filteredReplace = this.filterCondition(idp, replaced, nodeVariables, itpfFactory, aborter);

            newConditions.put(node.getKey(), filteredReplace);
        }

        return newConditions;
    }

    protected Map<INode, ITerm<?>> createNewTerms(final IDPProblem idp,
        final FilterReplacement filterReplacement) {

        final VarRenaming varSubst = filterReplacement.variableReplacement;
        final FunctionSymbolReplacement fsReplacement = filterReplacement.functionSymbolReplacement;

        final Map<INode, ITerm<?>> termReplacement =
            new LinkedHashMap<INode, ITerm<?>>();

        for (final Map.Entry<INode, ? extends ITerm<?>> nodeEntry : idp.getIdpGraph().getNodeMap().entrySet()) {
            final ITerm<?> newTerm =
                nodeEntry.getValue().replaceAllFunctionSymbols(fsReplacement).applySubstitution(
                    varSubst);
            termReplacement.put(nodeEntry.getKey(), newTerm);
        }
        return termReplacement;
    }

    protected IQTermSet createNewQ(final IDPProblem idp,
        final FilterReplacement filterReplacement) {

        final VarRenaming varSubst = filterReplacement.variableReplacement;
        final FunctionSymbolReplacement fsReplacement = filterReplacement.functionSymbolReplacement;

        final IQTermSet oldQ = idp.getIdpGraph().getQ();
        final Set<IFunctionApplication<?>> newQTerms = new LinkedHashSet<IFunctionApplication<?>>();

        for (final IFunctionApplication<?> t : oldQ.getUserDefinedTerms()) {
            newQTerms.add(t.replaceAllFunctionSymbols(fsReplacement).applySubstitution(
                varSubst));
        }

        return new IQTermSet(newQTerms, oldQ.getPredefinedMode(), oldQ.getPredefinedMap());
    }

    private ImmutableSet<IDPSubGraph> createNewSubgraphs(final ImmutableSet<IDPSubGraph> subGraphs,
        final Map<IEdge, IEdge> edgeMap) {
        final Set<IDPSubGraph> newSubGraphs = new LinkedHashSet<IDPSubGraph>();

        for (final IDPSubGraph subGraph : subGraphs) {
            final Set<IEdge> newSubGraph = new LinkedHashSet<IEdge>();
            for (final IEdge edge : subGraph.getEdges()) {
                newSubGraph.add(edgeMap.get(edge));
            }

            newSubGraphs.add(new IDPSubGraph(ImmutableCreator.create(newSubGraph)));
        }

        return ImmutableCreator.create(newSubGraphs);
    }

    protected Itpf filterCondition(final IDPProblem idp, final Itpf condition, final Set<IVariable<?>> retainedFreeVariables, final ItpfFactory itpfFactory, final Abortion aborter) throws AbortionException {
        switch (this.filterMode) {
        case QUANTIFY_FILTERED_VARIABLES:
            final Set<IVariable<?>> freeVariables = new LinkedHashSet<IVariable<?>>(condition.getFreeVariables());
            freeVariables.removeAll(retainedFreeVariables);
            return itpfFactory.quantifyExist(freeVariables, condition);

        case REMOVE_FILTERED_ATOMS:
            final LinkedHashSet<IVariable<?>> retainedVariables = new LinkedHashSet<IVariable<?>>(retainedFreeVariables);
            retainedVariables.addAll(condition.getBoundVariables());
            final ItpfFilterVariables variablesFilter = new ItpfFilterVariables(ImmutableCreator.create(retainedVariables));
            final ExecutionResult<Conjunction<Itpf>, Itpf> fitered = variablesFilter.process(idp, condition, ImplicationType.SOUND, ApplicationMode.Multistep, aborter);
            return itpfFactory.createAnd(fitered.asCollection());

        default:
            throw new UnsupportedOperationException("unknown filter type");
        }
    }


    protected static class ItpfFilterVariables extends ContextFreeItpfReplaceRule {

        private final ImmutableSet<IVariable<?>> retainedVariables;

        public ItpfFilterVariables(final ImmutableSet<IVariable<?>> retainedVariables) {
            super(new ExportableString("[i] FilterFreeVariables"), new ExportableString("[i] FilterFreeVariables"));
            this.retainedVariables = retainedVariables;
        }

        @Override
        public boolean isSound() {
            return true;
        }

        @Override
        public boolean isComplete() {
            return false;
        }

        @Override
        public boolean isApplicable(final IDPProblem idp) {
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
            return this.equals(mark);
        }

        @Override
        protected ExecutionResult<? extends QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
            final ReplaceContext.ReplaceContextSkeleton context,
            final ItpfAndWrapper precondition,
            final Set<ITerm<?>> s,
            final ItpfAtom atom,
            final Boolean positive,
            final ImplicationType executionRequirements,
            final ApplicationMode mode,
            final Abortion aborter) throws AbortionException {
            if (!this.retainedVariables.containsAll(atom.getVariables())) {
                if (!executionRequirements.isComplete()) {
                    return this.getEmptyReturn(idp.getItpfFactory(), ImplicationType.SOUND, ApplicationMode.SingleStep);
                } else if (!executionRequirements.isSound()) {
                    return this.getUnsatReturn(ImplicationType.COMPLETE, ApplicationMode.SingleStep);
                } else {
                    throw new UnsupportedOperationException("equivalence not supported");
                }
            }
            return null;
        }
    }

    public static class AbstractFilterProof extends DefaultProof implements
    IDPExportable {

        final int EXPORT_COLCOUNT = 10;
        private final FilterReplacement filter;

        public AbstractFilterProof(
                final FilterReplacement filter) {
            this.filter = filter;
        }

        @Override
        public final String toString() {
            return this.export(new PLAIN_Util());
        }

        @Override
        public final String export(final Export_Util o) {
            return this.export(o, IDPExportable.DEFAULT_LEVEL);
        }

        @Override
        public final String export(final Export_Util o,
            final VerbosityLevel verbosityLevel) {
            final StringBuilder sb = new StringBuilder();
            this.export(sb, o, verbosityLevel);
            return sb.toString();
        }

        @Override
        public void export(final StringBuilder sb,
            final Export_Util o,
            final VerbosityLevel level) {
            sb.append("Generated filter:");
            sb.append(o.newline());
            this.filter.export(sb, o, level);
        }
    }

}
