package aprove.verification.idpframework.Processors.Filters;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Algorithms.UsableRules.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class VariablePartitioning extends AbstractIDPFilter<Result, TIDPProblem> {

    public static enum Mode {
        UNNEEDED_ARGS, SINGLE_PARTITIONS, SINGLE_PARTITION_AND_ORIGINAL;
    }

    public static class Arguments {
        public Mode mode = Mode.SINGLE_PARTITIONS;
    }

    private final Mode mode;
    private final float minReductionFactorThreshold = 0.7f;

    @ParamsViaArgumentObject
    public VariablePartitioning(final Arguments arguments) {
        super("VariablePartitioning", FilterMode.REMOVE_FILTERED_ATOMS);
        this.mode = arguments.mode;
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
    protected Result processIDPProblem(final TIDPProblem idp, final Abortion aborter) throws AbortionException {

        final VariablePartitionGraph variablePartitioning = new VariablePartitionGraph();

        this.generateNodeTermEqClasses(idp, variablePartitioning, aborter);
        this.generateLoopRenamingEqClasses(idp, variablePartitioning, aborter);
        this.generateNodeCondEqClasses(idp, variablePartitioning, aborter);
        this.generateEdgeEqClasses(idp, variablePartitioning, aborter);

        final Set<ImmutableSet<VariablePartitionPos>> partitions = variablePartitioning.getPartitions();

        final Collection<FilterReplacement> filters = this.createFilters(idp, partitions, aborter);

        final Set<IDPProblem> newIDPs = new LinkedHashSet<>();

        final ImmutableSet<IVariable<?>> idpVars = idp.getIdpGraph().getVariables();
        final int idpVarsSize = idpVars.size();

        for (final FilterReplacement filter : filters) {
            final IDPProblem newIDP = this.createNewIDP(idp, filter, aborter);

            final ImmutableSet<IVariable<?>> newIDPVars = newIDP.getIdpGraph().getVariables();

            if (newIDPVars.size() < idpVarsSize * this.minReductionFactorThreshold) {
                newIDPs.add(newIDP);
            }
        }

        /*
         * FIXME:
         * There is no implementation for TIDPProblem.equals, so if a new object for idp is added to newIDPs we continue
         * with two variants of it.
         */
        if (!newIDPs.isEmpty()) {
            newIDPs.add(idp);
            return ResultFactory.provedOr(newIDPs, YNMImplication.SOUND,
                new VariablePartitioningProof(ImmutableCreator.create(partitions), ImmutableCreator.create(filters)));
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    private void generateNodeTermEqClasses(final IDPProblem idp,
        final VariablePartitionGraph variablePartitioning,
        final Abortion aborter) {
        final IDependencyGraph graph = idp.getIdpGraph();

        for (final Map.Entry<INode, ? extends ITerm<?>> nodeTerm : graph.getNodeMap().entrySet()) {
            this.collectVarPositions(variablePartitioning, IActiveContext.EMPTY_CONTEXT, ITerm.EMPTY_VARIABLES,
                nodeTerm.getValue());
            if (graph.isInitialRewriteNode(nodeTerm.getKey())) {
                final ITerm<?> t = nodeTerm.getValue();
                if (!t.isVariable()) {
                    for (final ITerm<?> arg : ((IFunctionApplication<?>) t).getArguments()) {
                        this.collectCheckedPositions(variablePartitioning, arg);
                    }
                }
            }
        }
    }

    private void generateEdgeEqClasses(final IDPProblem idp,
        final VariablePartitionGraph variablePartitioning,
        final Abortion aborter) throws AbortionException {
        final IDependencyGraph graph = idp.getIdpGraph();
        for (final Map.Entry<IEdge, Itpf> entry : graph.getEdgeConditions().entrySet()) {
            this.typeItpf(entry.getValue(), variablePartitioning);
        }
    }

    /**
     * @param idp
     * @param variablePartitioning
     * @param aborter
     * @throws AbortionException
     */
    private void generateNodeCondEqClasses(final IDPProblem idp,
        final VariablePartitionGraph variablePartitioning,
        final Abortion aborter) throws AbortionException {
        for (final Map.Entry<INode, Itpf> nodeCondition : idp.getIdpGraph().getNodeConditions().entrySet()) {
            this.typeItpf(nodeCondition.getValue(), variablePartitioning);
            aborter.checkAbortion();
        }
    }

    private void generateLoopRenamingEqClasses(final IDPProblem idp,
        final VariablePartitionGraph variablePartitioning,
        final Abortion aborter) {
        for (final Map.Entry<INode, VarRenaming> renaming : idp.getIdpGraph().getLoopRenamings().entrySet()) {
            for (final Map.Entry<IVariable<?>, ? extends IVariable<?>> substEntry : renaming.getValue().getMap().entrySet()) {
                this.makeEquivalent(variablePartitioning, substEntry.getKey(), substEntry.getValue());
            }
        }
    }

    private void typeItpf(final Itpf itpf, final VariablePartitionGraph variablePartitioning) {

        for (final ItpfConjClause clause : itpf.getClauses()) {
            for (final ItpfAtom atom : clause.getLiterals().keySet()) {
                if (atom.isItp()) {
                    this.typeItp((ItpfItp) atom, variablePartitioning);
                } else if (atom.isPoly()) {
                    final ItpfPolyAtom<?> polyAtom = (ItpfPolyAtom<?>) atom;
                    this.makeTermsEquivalent(variablePartitioning, polyAtom.getPoly().getVariables());
                } else if (atom.isImplication()) {
                    final ItpfImplication implication = (ItpfImplication) atom;
                    this.typeItpf(implication.getPrecondition(), variablePartitioning);
                    this.typeItpf(implication.getConclusion(), variablePartitioning);
                } else {
                    this.makeTermsEquivalent(variablePartitioning, atom.getTerms(false));
                }
            }
        }
    }

    private void typeItp(final ItpfItp itp, final VariablePartitionGraph variablePartitioning) {
        switch (itp.getRelation()) {
        case EQ:
        case ABSTRACT_GE:
        case ABSTRACT_GT:
        case ABSTRACT_WEAK_GT:
            this.makeTermsEquivalent(variablePartitioning, itp.getL(), itp.getR());
            return;
        case TO_SYM_TRANS:
        case TO_TRANS:
            this.typeItpLeftTermRelations(itp.getL(), variablePartitioning);
            this.makeTermsEquivalent(variablePartitioning, itp.getL(), itp.getR());
            return;
        case TO:
        case TO_PLUS:
            this.typeItpLeftTermRelations(itp.getL(), variablePartitioning);
            this.addImplication(variablePartitioning, itp.getL(), itp.getR());
            return;
        default:
            this.makeTermsEquivalent(variablePartitioning, itp.getL(), itp.getR());
        }
    }

    private void typeItpLeftTermRelations(final ITerm<?> l, final VariablePartitionGraph variablePartitioning) {
        if (!l.isVariable()) {
            final IFunctionApplication<?> faL = (IFunctionApplication<?>) l;
            final IFunctionSymbol<?> rootFs = faL.getRootSymbol();

            final PredefinedFunction<?, ?> predefinedFunction = PredefinedUtil.getPredefinedFunction(rootFs);
            if (predefinedFunction != null) {
                if (predefinedFunction.isRelation() || predefinedFunction.isArithmetic()) {
                    variablePartitioning.addCheckedVars(faL.getVariables());
                    this.makeTermsEquivalent(variablePartitioning, faL.getArguments());
                    return;
                }
            }

            for (int i = rootFs.getArity() - 1; i >= 0; i--) {
                this.typeItpLeftTermRelations(faL.getArgument(i), variablePartitioning);
            }
        }
    }

    private void addImplication(final VariablePartitionGraph variablePartitioning,
        final Set<IVariable<?>> sourceVars,
        final Set<IVariable<?>> dependentVars) {
        for (final IVariable<?> sourceVar : sourceVars) {
            final VariablePartitionPos sourceVarPos = new VariablePartitionPos(sourceVar);
            for (final IVariable<?> dependentVar : dependentVars) {
                variablePartitioning.addEdgeVariable(new VariablePartitionPos(dependentVar), sourceVarPos);
            }
        }
    }

    private void addImplication(final VariablePartitionGraph variablePartitioning,
        final ITerm<?> sourceTerm,
        final ITerm<?> dependentTerm) {
        this.addImplication(variablePartitioning, sourceTerm.getVariables(), dependentTerm.getVariables());

        this.collectVarPositions(variablePartitioning, IActiveContext.EMPTY_CONTEXT, ITerm.EMPTY_VARIABLES, sourceTerm);
        this.collectVarPositions(variablePartitioning, IActiveContext.EMPTY_CONTEXT, ITerm.EMPTY_VARIABLES,
            dependentTerm);
    }

    private void makeEquivalent(final VariablePartitionGraph variablePartitioning,
        final Collection<? extends IVariable<?>> variables) {

        if (variables.size() <= 1) {
            return;
        }

        final Iterator<? extends IVariable<?>> varIterator = variables.iterator();

        final IVariable<?> firstVar = varIterator.next();

        while (varIterator.hasNext()) {
            this.makeEquivalent(variablePartitioning, firstVar, varIterator.next());
        }
    }

    private void makeEquivalent(final VariablePartitionGraph variablePartitioning,
        final IVariable<?> var1,
        final IVariable<?> var2) {
        final VariablePartitionPos var1Pos = new VariablePartitionPos(var1);
        final VariablePartitionPos var2Pos = new VariablePartitionPos(var2);
        variablePartitioning.addEdgeVariable(var1Pos, var2Pos);
        variablePartitioning.addEdgeVariable(var2Pos, var1Pos);
    }

    private void makeTermsEquivalent(final VariablePartitionGraph variablePartitioning,
        final Collection<? extends ITerm<?>> terms) {

        if (terms.size() <= 1) {
            final ITerm<?> firstTerm = terms.iterator().next();
            this.makeEquivalent(variablePartitioning, firstTerm.getVariables());
            this.collectVarPositions(variablePartitioning, IActiveContext.EMPTY_CONTEXT, ITerm.EMPTY_VARIABLES,
                firstTerm);
            return;
        } else {
            final Iterator<? extends ITerm<?>> termIterator = terms.iterator();

            final ITerm<?> firstTerm = termIterator.next();
            while (termIterator.hasNext()) {
                this.makeTermsEquivalent(variablePartitioning, firstTerm, termIterator.next());
            }
        }
    }

    private void makeTermsEquivalent(final VariablePartitionGraph variablePartitioning,
        final ITerm<?> t1,
        final ITerm<?> t2) {
        final LinkedHashSet<IVariable<?>> allVariables = new LinkedHashSet<IVariable<?>>();
        t1.collectVariables(allVariables);
        t2.collectVariables(allVariables);
        this.makeEquivalent(variablePartitioning, allVariables);

        this.collectVarPositions(variablePartitioning, IActiveContext.EMPTY_CONTEXT, ITerm.EMPTY_VARIABLES, t1);
        this.collectVarPositions(variablePartitioning, IActiveContext.EMPTY_CONTEXT, ITerm.EMPTY_VARIABLES, t2);
    }

    private void collectVarPositions(final VariablePartitionGraph variablePartitioning,
        final IActiveContext pathToRoot,
        final ImmutableSet<IVariable<?>> lockedVariables,
        final ITerm<?> t) {
        if (!t.isVariable()) {
            final IFunctionApplication<?> faL = (IFunctionApplication<?>) t;
            final IFunctionSymbol<?> rootFs = faL.getRootSymbol();

            final LinkedHashSet<IVariable<?>> newLockedVariables = new LinkedHashSet<IVariable<?>>(lockedVariables);
            for (int i = rootFs.getArity() - 1; i >= 0; i--) {
                final ITerm<?> arg = faL.getArgument(i);
                if (arg.isVariable()) {
                    if (newLockedVariables.add((IVariable<?>) arg)) {
                        final VariablePartitionPos varPos = new VariablePartitionPos((IVariable<?>) arg);
                        final ImmutableList<IActiveAtom> context =
                            pathToRoot.add(IActiveAtom.create(rootFs, i)).getContext();

                        for (int c = context.size() - 1; c >= 0; c--) {
                            final VariablePartitionPos next = new VariablePartitionPos(context.get(c));
                            variablePartitioning.addEdgeVariable(varPos, next);
                        }
                    }
                }
            }

            for (int i = rootFs.getArity() - 1; i >= 0; i--) {
                this.collectVarPositions(variablePartitioning, pathToRoot.add(IActiveAtom.create(rootFs, i)),
                    ImmutableCreator.create(newLockedVariables), faL.getArgument(i));
            }
        }
    }

    private void collectCheckedPositions(final VariablePartitionGraph variablePartitioning, final ITerm<?> t) {
        if (!t.isVariable()) {
            final IFunctionApplication<?> faL = (IFunctionApplication<?>) t;
            final IFunctionSymbol<?> rootFs = faL.getRootSymbol();

            for (int i = rootFs.getArity() - 1; i >= 0; i--) {
                final VariablePartitionPos rootFsPos = new VariablePartitionPos(IActiveAtom.create(rootFs, i));
                variablePartitioning.addCheckedPosition(rootFsPos);
                final ITerm<?> arg = faL.getArgument(i);
                if (!arg.isVariable()) {

                    this.collectCheckedPositions(variablePartitioning, arg);
                    final IFunctionApplication<?> argFa = (IFunctionApplication<?>) arg;
                    final IFunctionSymbol<?> argFs = argFa.getRootSymbol();

                    for (int j = argFs.getArity() - 1; j >= 0; j--) {
                        final VariablePartitionPos argFsPos = new VariablePartitionPos(IActiveAtom.create(argFs, j));
                        variablePartitioning.addEdgeVariable(rootFsPos, argFsPos);
                    }

                } else {
                    variablePartitioning.addEdgeVariable(rootFsPos, new VariablePartitionPos((IVariable<?>) arg));
                }
            }
        }
    }

    private Collection<FilterReplacement> createFilters(final IDPProblem idp,
        final Set<ImmutableSet<VariablePartitionPos>> partitions,
        final Abortion aborter) throws AbortionException {
        final Set<FilterReplacement> res = new LinkedHashSet<FilterReplacement>();

        if (this.mode == Mode.UNNEEDED_ARGS) {
            final Map<IFunctionSymbol<?>, ArrayList<Boolean>> retainedPositions =
                this.initRetainedPositions(idp.getIdpGraph().getFunctionSymbols());

            for (final Set<VariablePartitionPos> partition : partitions) {
                this.retainPositions(retainedPositions, partition);
                this.retainEdgePositions(retainedPositions, idp.getIdpGraph());
            }

            final FunctionSymbolReplacement fsReplacementMap = this.createFsReplaceMap(idp, retainedPositions, aborter);

            res.add(new FilterReplacement(fsReplacementMap, VarRenaming.EMPTY_RENAMING));
        } else {
            // single partitions
            for (final Set<VariablePartitionPos> partition : partitions) {
                final Map<IFunctionSymbol<?>, ArrayList<Boolean>> retainedPositions =
                    this.initRetainedPositions(idp.getIdpGraph().getFunctionSymbols());

                this.retainPositions(retainedPositions, partition);
                this.retainEdgePositions(retainedPositions, idp.getIdpGraph());

                final FunctionSymbolReplacement fsReplacementMap = this.createFsReplaceMap(idp, retainedPositions, aborter);

                res.add(new FilterReplacement(fsReplacementMap, VarRenaming.EMPTY_RENAMING));
            }
        }

        if (this.mode == Mode.SINGLE_PARTITION_AND_ORIGINAL) {
            res.add(new FilterReplacement(new FunctionSymbolReplacement(), VarRenaming.EMPTY_RENAMING));
        }
        return res;
    }

    private Map<IFunctionSymbol<?>, ArrayList<Boolean>> initRetainedPositions(final ImmutableSet<IFunctionSymbol<?>> functionSymbols) {
        final LinkedHashMap<IFunctionSymbol<?>, ArrayList<Boolean>> res =
            new LinkedHashMap<IFunctionSymbol<?>, ArrayList<Boolean>>();

        for (final IFunctionSymbol<?> fs : functionSymbols) {
            if (fs.getSemantics() == null) {
                final ArrayList<Boolean> retainedArgs = new ArrayList<Boolean>(fs.getArity());

                for (int i = fs.getArity() - 1; i >= 0; i--) {
                    retainedArgs.add(Boolean.FALSE);
                }

                res.put(fs, retainedArgs);
            }
        }

        return res;
    }

    private void retainPositions(final Map<IFunctionSymbol<?>, ArrayList<Boolean>> retainedPositions,
        final Set<VariablePartitionPos> partition) {
        for (final VariablePartitionPos pos : partition) {
            final IActiveAtom active = pos.getActiveAtom();
            if (active != null) {
                if (active.fs.getSemantics() == null) {
                    retainedPositions.get(active.fs).set(active.pos, Boolean.TRUE);
                }
            }
        }
    }

    private void retainEdgePositions(final Map<IFunctionSymbol<?>, ArrayList<Boolean>> retainedPositions,
        final IDependencyGraph idpGraph) {
        for (final IEdge edge : idpGraph.getEdges()) {
            final IActiveContext activeContext = IActiveContext.create(idpGraph.getTerm(edge.from), edge.fromPos);
            for (final IActiveAtom active : activeContext) {
                if (active.fs.getSemantics() == null) {
                    retainedPositions.get(active.fs).set(active.pos, Boolean.TRUE);
                }
            }
        }
    }

    public static class VariablePartitioningProof extends DefaultProof implements IDPExportable {

        final int EXPORT_COLCOUNT = 10;
        private final ImmutableSet<ImmutableSet<VariablePartitionPos>> partitions;
        private final ImmutableCollection<FilterReplacement> filters;

        public VariablePartitioningProof(final ImmutableSet<ImmutableSet<VariablePartitionPos>> immutableSet,
                final ImmutableCollection<FilterReplacement> filters) {
            this.partitions = immutableSet;
            this.filters = filters;
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
        public final String export(final Export_Util o, final VerbosityLevel verbosityLevel) {
            final StringBuilder sb = new StringBuilder();
            this.export(sb, o, verbosityLevel);
            return sb.toString();
        }

        @Override
        public void export(final StringBuilder sb, final Export_Util o, final VerbosityLevel level) {
            if (this.filters.size() == 1) {
                sb.append("Generated filter:");
            } else {
                sb.append("Generated " + this.filters.size() + " different filters:");
            }
            sb.append(o.linebreak());

            for (final FilterReplacement filter : this.filters) {
                filter.export(sb, o, level);

                if (this.filters.size() > 1) {
                    sb.append(o.hline());
                }
            }
        }
    }
}
