package aprove.verification.complexity.CIdtProblem.Processors;

import java.util.*;
import java.util.Map.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CIdtProblem.*;
import aprove.verification.complexity.CIdtProblem.Utility.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.FreshVarGenerator;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Marcel Klinzing
 */
public class CIdtPathCollapseProcessor extends CIdtProcessor<Result> {

    private int collapseSSelfLoops;

    @ParamsViaArgumentObject
    public CIdtPathCollapseProcessor(Arguments arguments) {
        super("CIdtPathCollapse");
        this.collapseSSelfLoops = arguments.collapseSSelfLoops;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return false;
    }

    @Override
    protected boolean isCIdtApplicable(CIdtProblem idt) {
        return true;
    }

    @Override
    protected Result processCIdtProblem(CIdtProblem idt, Abortion aborter)
            throws AbortionException {

        List<CIdtCollapsedPathsResult> results = new ArrayList<CIdtCollapsedPathsResult>();
        List<List<INode>> priorizedNodes = this.priorize(idt);
        priorizedNodes = this.sort(idt, priorizedNodes);
        CIdtCollapsedPathsResult collapsedPathsResult = this.collapsePaths(idt, priorizedNodes, aborter);
        CIdtProblem newCIdt = idt;


        while (! (collapsedPathsResult == null)) {
            results.add(collapsedPathsResult);
            newCIdt = this.createResult(newCIdt, collapsedPathsResult);
            priorizedNodes = this.priorize(newCIdt);
            priorizedNodes = this.sort(newCIdt, priorizedNodes);
            collapsedPathsResult = this.collapsePaths(newCIdt, priorizedNodes, aborter);
        }

        if (this.collapseSSelfLoops > 0) {
            Pair<CIdtProblem, List<CIdtCollapsedPathsResult>> collapsedSSelfLoopsResult =
                this.collapseSSelfLoops(newCIdt, aborter);
            newCIdt = collapsedSSelfLoopsResult.x;
            results.addAll(collapsedSSelfLoopsResult.y);
        }



        if (newCIdt != idt) {

            ImmutableSet<IEdge> newS = CIdtProblem.cleanupS(newCIdt.getIdpGraph(), newCIdt.getS(), newCIdt.getK());
            newCIdt = newCIdt.change(newS);

            final CIdtPathCollapseProof proof =
                new CIdtPathCollapseProof(results);
            return  ResultFactory.proved(newCIdt, BothBounds.create(), proof);
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    private List<List<INode>> sort(CIdtProblem idt, List<List<INode>> priorizedNodes) {

        IDependencyGraph graph = idt.getIdpGraph();
        List<List<INode>> newPriorizdeNodes = new ArrayList<>();

        for (List<INode> oldNodeSet : priorizedNodes) {

            Map<INode, Integer> nodeToInDegree = new LinkedHashMap<>();

            for (INode node : oldNodeSet) {
                nodeToInDegree.put(node, graph.getInDegree(node, EdgeType.INF_EDGE_TYPES));
            }

            List<INode> sortedNodes = new ArrayList<>();
            for (INode node : oldNodeSet) {
                int nodeInDegree = nodeToInDegree.get(node);
                int pos = 0;
                for (INode comp : sortedNodes) {
                    if (nodeInDegree >= nodeToInDegree.get(comp)) {
                        pos++;
                    } else {
                        break;
                    }
                }

               sortedNodes.add(pos, node);
            }

            newPriorizdeNodes.add(sortedNodes);
        }
        return newPriorizdeNodes;
    }

    private List<List<INode>> priorize(CIdtProblem idt) {

        List<List<INode>> prior = new ArrayList<>();

        IDependencyGraph graph = idt.getIdpGraph();
        List<INode> priorNodes1 = new ArrayList<>();
        List<INode> priorNodes2 = new ArrayList<>();

        for (INode node : graph.getNodes()) {
            if (graph.getOutDegree(node, EdgeType.INF_EDGE_TYPES) > 1) {
                priorNodes1.add(node);

            } else {

                priorNodes2.add(node);
            }
        }

        final int lowestPriority = 0;
        Map<INode, Integer> priorAfterTermsMap = this.priorizeAfterTerms(graph, lowestPriority);
        int highestPriority = lowestPriority;

        for (int i : priorAfterTermsMap.values()) {
            if (i > highestPriority) {
                highestPriority = i;
            }
        }

        Map<Integer, List<INode>> priorMap = new LinkedHashMap<>();

        for (int i = lowestPriority; i <= highestPriority; i++) {
            priorMap.put(i, new ArrayList<INode>());
        }



        for (INode node : priorNodes2) {
            int priority = priorAfterTermsMap.get(node);
            priorMap.get(priority).add(node);
        }

        for (INode node : priorNodes1) {
            int priority = priorAfterTermsMap.get(node);
            priorMap.get(priority).add(node);
        }

        for (int i = lowestPriority; i <= highestPriority; i++) {
            prior.add(priorMap.get(i));
        }

        return prior;
    }

    private Map<INode, Integer> priorizeAfterTerms(IDependencyGraph graph, int lowestPriority) {

        Map<INode, Integer> priorMap = new LinkedHashMap<>();

        Set<IFunctionSymbol<?>> definedFSymbs = graph.getDefinedSymbols();

        for (INode node : graph.getNodes()) {
            ITerm<?> nodeTerm = graph.getTerm(node);

            if (nodeTerm.isVariable()) {
                priorMap.put(node, lowestPriority);
                continue;
            }

            IFunctionApplication<?> nodeFA =  (IFunctionApplication<?>) nodeTerm;


            if (PredefinedUtil.hasPredefinedFunction(nodeFA)) {
                priorMap.put(node, lowestPriority);
                continue;
            } else if (!definedFSymbs.contains(nodeFA.getRootSymbol())) {
                priorMap.put(node, lowestPriority + 1);
                continue;
            }

            boolean argPriorize = false;
            for (ITerm<?> nodeArg : nodeFA.getArguments()) {
                if (argPriorize) {
                    break;
                }
                Set<IFunctionSymbol<?>> fS = new LinkedHashSet<>();
                nodeArg.collectFunctionSymbols(fS);
                for (IFunctionSymbol<?> fSymbol : fS) {
                    if (!definedFSymbs.contains(fSymbol)) {
                        argPriorize = true;
                    }
                }
            }
            if (argPriorize) {
                priorMap.put(node, lowestPriority + 2);
            } else {
                priorMap.put(node, lowestPriority + 3);
            }
        }



        return priorMap;
    }

    private Pair<CIdtProblem, List<CIdtCollapsedPathsResult>> collapseSSelfLoops(CIdtProblem newCIdt,
        Abortion aborter) throws AbortionException {

        Set<EdgeType> infTypes = new LinkedHashSet<EdgeType>();
        infTypes.add(EdgeType.INF);
        infTypes.add(EdgeType.REWRITE_INF);

        List<CIdtCollapsedPathsResult> results = new ArrayList<CIdtCollapsedPathsResult>();

        EdgeConditionMap newEdgeConditions =
            new EdgeConditionMap(newCIdt.getIdpGraph().getItpfFactory(), newCIdt.getIdpGraph().getFreshVarGenerator(),
                newCIdt.getIdpGraph().getEdgeConditions());

        Map<IEdge, Integer> collapsedEdges = new LinkedHashMap<IEdge, Integer>();

        Set<IEdge> newS = new LinkedHashSet<IEdge>(newCIdt.getS());
        Set<IEdge> newK = new LinkedHashSet<IEdge>(newCIdt.getK());

        CIdtCollapsedPathsResult result;
        for (IEdge edge : newCIdt.getS()) {
            if (edge.from == edge.to && newCIdt.getIdpGraph().getOutDegree(edge.from, infTypes) == 1) {
                newS.remove(edge);
                this.compactSelfLoops(newCIdt, edge, this.collapseSSelfLoops, EdgeType.INF, newEdgeConditions, aborter);
                collapsedEdges.put(edge, this.collapseSSelfLoops);
                if (newEdgeConditions.get(edge) != null) {
                    if (newEdgeConditions.get(edge).isFalse()) {
                        newK.add(edge);
                    } else {
                        newS.add(edge);
                    }
                }

                result =
                    new CIdtCollapsedPathsResult(CollectionUtil.immutableCollectionMap(new CollectionMap<Pair<IEdge, IEdge>, IEdge>()),
                        ImmutableCreator.create(newEdgeConditions.getMap()), ImmutableCreator.create(newS), ImmutableCreator.create(newK),
                        ImmutableCreator.create(collapsedEdges));
                results.add(result);
                newCIdt = this.createResult(newCIdt, result);
                newEdgeConditions =
                    new EdgeConditionMap(newCIdt.getIdpGraph().getItpfFactory(),
                        newCIdt.getIdpGraph().getFreshVarGenerator(), newCIdt.getIdpGraph().getEdgeConditions());
            }
        }

        return new Pair<CIdtProblem, List<CIdtCollapsedPathsResult>>(newCIdt, results);
    }

    private void compactSelfLoops(CIdtProblem idt,
        IEdge edge,
        int howOften,
        EdgeType collapsedEdgeType,
        EdgeConditionMap newEdgeConditions,
        Abortion aborter) throws AbortionException {

        IDependencyGraph graph = idt.getIdpGraph();
        FreshVarGenerator freshNames = graph.getFreshVarGenerator();

        final PolyFactory polyFactory;
        if (idt.getPolyInterpretation() != null) {
            polyFactory = idt.getPolyInterpretation().getFactory();
        } else {
            polyFactory = null;
        }

        List<ImmutablePair<IEdge, VarRenaming>> ren = new ArrayList<ImmutablePair<IEdge, VarRenaming>>();
        VarRenaming varRenaming =
            ItpfUtil.getVariableRenaming(polyFactory, graph.getTerm(edge.to).getVariables(), freshNames);
        ren.add(new ImmutablePair<IEdge, VarRenaming>(edge, varRenaming));
        for (int i = 0; i < howOften; i++) {
            if (i < howOften - 1) {
                varRenaming =
                    ItpfUtil.getVariableRenaming(polyFactory, graph.getTerm(edge.to).getVariables(), freshNames);
                ren.add(new ImmutablePair<IEdge, VarRenaming>(edge, varRenaming));
            } else {
                ren.add(new ImmutablePair<IEdge, VarRenaming>(edge, graph.getLoopRenaming(edge.from)));
            }
        }
        VariableRenamedPath renamedPath = VariableRenamedPath.create(graph, ImmutableCreator.create(ren));

        final Itpf pathCondition = graph.itpfPath(renamedPath, PathQuantificationMode.InnerSteps);

        final ItpfSchedulerProof<Itpf, GenericItpfRule<?>> proof =
            new ItpfSchedulerProof<Itpf, GenericItpfRule<?>>(idt, pathCondition, idt.getItpfFactory().createTrue());
        ItpfStrategy.HIDDEN_SIMPLIFICATION.getStrategy().apply(proof, ImplicationType.SOUND, aborter);

        newEdgeConditions.putFalse(edge);
        newEdgeConditions.putOr(edge,
            graph.getItpfFactory().createAnd(proof.getLastFormulaStates(), graph.getFreshVarGenerator()));

        final IEdge typeSubstractedEdge =
            IEdge.create(edge.from, edge.fromPos, edge.to, edge.type.subtractType(collapsedEdgeType));
        newEdgeConditions.putOr(typeSubstractedEdge, graph.getCondition(edge));
    }

    private CIdtProblem createResult(CIdtProblem idt,
        CIdtCollapsedPathsResult collapsResult) {

        IDependencyGraph newGraph = idt.getIdpGraph().change(
            null,
            collapsResult.newEdgeConditions,
            null,
            null,
            null,
            this);

        ImmutableSet<IEdge> newS = CIdtProblem.cleanupS(newGraph, collapsResult.newS, collapsResult.newK);

        CIdtProblem newCIdt = idt.change(newGraph, newS, collapsResult.newK);

        return newCIdt;
    }

    private CIdtCollapsedPathsResult collapsePaths(CIdtProblem idt, List<List<INode>> priorized, Abortion aborter)
            throws AbortionException {

        IDependencyGraph graph = idt.getIdpGraph();

        Set<IEdge> newS = new LinkedHashSet<IEdge>(idt.getS());
        Set<IEdge> newK = new LinkedHashSet<IEdge>(idt.getK());

        final CollectionMap<Pair<IEdge, IEdge>, IEdge> splitEdges = new CollectionMap<Pair<IEdge, IEdge>, IEdge>();

        final EdgeConditionMap newEdgeConditions =
            new EdgeConditionMap(idt.getIdpGraph().getItpfFactory(), idt.getIdpGraph().getFreshVarGenerator(),
                idt.getIdpGraph().getEdgeConditions());

        Set<EdgeType> infTypes = new LinkedHashSet<EdgeType>();
        infTypes.add(EdgeType.INF);
        infTypes.add(EdgeType.REWRITE_INF);

        for (List<INode> nodes : priorized) {

            for (INode node : nodes) {

                if (graph.getPosDependentOutDegree(node, infTypes) == 1) {

                    Set<IEdge> succEdges = new LinkedHashSet<>();
                    this.collectInfSuccEdges(succEdges, graph, node);

                    if (Globals.useAssertions) {
                        assert (!succEdges.isEmpty());
                    }

                    Set<IEdge> succEdgesInS = new LinkedHashSet<>();
                    for (IEdge edge : succEdges) {
                        if (newS.contains(edge)) {
                            succEdgesInS.add(edge);
                        }
                    }

                    int inDegree = graph.getInDegree(node, infTypes);
                    if (inDegree != 0) {
                        Set<IEdge> preEdges = new LinkedHashSet<>();
                        this.collectInfPreEdges(preEdges, graph, node);
                        for (IEdge preEdge : preEdges) {

                            if (this.shouldBeCollapsed(preEdge, succEdges, graph)) {
                                for (IEdge succEdge : succEdges) {

                                    Pair<IEdge, IEdge> path = new Pair<IEdge, IEdge>(preEdge, succEdge);

                                    IEdge newEdge = null;
                                    if (preEdges.size() == 1) {
                                        newEdge =
                                            this.compactPath(idt, path, splitEdges, EdgeType.INF, newEdgeConditions, true,
                                                aborter);
                                    } else {
                                        newEdge =
                                            this.compactPath(idt, path, splitEdges, EdgeType.INF, newEdgeConditions, false,
                                                aborter);
                                    }

                                    if (newS.contains(preEdge)) {
                                        newS.remove(preEdge);
                                        newS.add(newEdge);
                                    } else if (succEdgesInS.contains(succEdge)) {
                                        newS.add(newEdge);
                                    }
                                }

                            }

                            if (!splitEdges.isEmpty()) {
                                return new CIdtCollapsedPathsResult(CollectionUtil.immutableCollectionMap(splitEdges),
                                    ImmutableCreator.create(newEdgeConditions.getMap()), ImmutableCreator.create(newS),
                                    ImmutableCreator.create(newK),
                                    ImmutableCreator.create(new LinkedHashMap<IEdge, Integer>()));
                            }
                        }
                    }
                }
            }
        }

        return null;

    }

    private boolean shouldBeCollapsed(IEdge preEdge, Set<IEdge> succEdges, IDependencyGraph graph) {

        for (IEdge succEdge : succEdges) {

            if (succEdge.from == succEdge.to) {
                return false;
            }
            if (preEdge.from == succEdge.to && graph.getPosDependentOutDegree(preEdge.from, EdgeType.INF_EDGE_TYPES) > 1) {
                return false;
            }
        }
        return true;
    }

    private void collectInfSuccEdges(Set<IEdge> succEdges, IDependencyGraph graph, INode node) {
        for (Set<IEdge> edges : graph.getSuccessors(node).values()) {
            for (IEdge edge : edges) {
                if (edge.type.isInf()) {
                    succEdges.add(edge);
                }

            }
        }
    }

    private void collectInfPreEdges(Set<IEdge> preEdges, IDependencyGraph graph, INode node) {
        for (Set<IEdge> edges : graph.getPredecessors(node).values()) {
            for (IEdge edge : edges) {
                if (edge.type.isInf()) {
                    preEdges.add(edge);
                }

            }
        }
    }

    private boolean hasLoop(INode node, IDependencyGraph graph) {
        boolean hasLoop = false;
        for (Set<IEdge> edges : graph.getSuccessors(node).values()) {
            for (IEdge edge : edges) {
                if (edge.from == edge.to) {
                    hasLoop = true;
                    break;
                }
            }
        }
        return hasLoop;
    }

    /**
     * Introduce new edge
     */
    private IEdge compactPath(final CIdtProblem idt,
        final Pair<IEdge, IEdge> path,
        final CollectionMap<Pair<IEdge, IEdge>, IEdge> splitEdges,
        final EdgeType colapsedEdgeType,
        final EdgeConditionMap newEdgeConditions, boolean maybeDeleteLast, final Abortion aborter) throws AbortionException {

        final IDependencyGraph graph = idt.getIdpGraph();
        final FreshVarGenerator freshNames = graph.getFreshVarGenerator();

        final IEdge firstEdge = path.x;
        final IEdge lastEdge = path.y;
        final INode firstNode = firstEdge.from;

        final List<ImmutablePair<IEdge, VarRenaming>> ren =
            new ArrayList<ImmutablePair<IEdge, VarRenaming>>();

        final PolyFactory polyFactory;
        if (idt.getPolyInterpretation() != null) {
            polyFactory = idt.getPolyInterpretation().getFactory();
        } else {
            polyFactory = null;
        }

        VarRenaming varRenaming =
            ItpfUtil.getVariableRenaming(polyFactory, graph.getTerm(
                firstEdge.to).getVariables(), freshNames);
        ren.add(new ImmutablePair<IEdge, VarRenaming>(firstEdge, varRenaming));

        ren.add(new ImmutablePair<IEdge, VarRenaming>(lastEdge,
            lastEdge.to == firstNode ? graph.getLoopRenaming(firstNode)
                : VarRenaming.EMPTY_RENAMING));

        final VariableRenamedPath renamedPath =
            VariableRenamedPath.create(graph, ImmutableCreator.create(ren));

        Itpf pathCondition = graph.itpfPath(renamedPath, PathQuantificationMode.InnerSteps);

        VarRenaming renameBoundedVar = ItpfUtil.getVariableRenaming(polyFactory, pathCondition.getBoundVariables(), freshNames);
        pathCondition = pathCondition.applySubstitution(renameBoundedVar, true);


        final ItpfSchedulerProof<Itpf, GenericItpfRule<?>> proof = new ItpfSchedulerProof<Itpf, GenericItpfRule<?>>(idt,
                pathCondition,
                idt.getItpfFactory().createTrue());

        //ItpfStrategy.HIDDEN_SIMPLIFICATION.getStrategy().apply(proof, ImplicationType.SOUND, aborter);

        newEdgeConditions.putFalse(firstEdge);

        IEdge newEdge =
            IEdge.create(firstEdge.from, firstEdge.fromPos, lastEdge.to,
                colapsedEdgeType);

        newEdgeConditions.putOr(newEdge, graph.getItpfFactory().createAnd(
            proof.getLastFormulaStates(), graph.getFreshVarGenerator()));

        final IEdge firstTypeSubstractedEdge =
            IEdge.create(firstEdge.from, firstEdge.fromPos, firstEdge.to,
                firstEdge.type.subtractType(colapsedEdgeType));

        newEdgeConditions.putOr(firstTypeSubstractedEdge,
            graph.getCondition(firstEdge));

        Pair<IEdge, IEdge> firstAndLastEdge = new Pair<>(firstEdge, lastEdge);
        if (firstTypeSubstractedEdge.type != EdgeType.NO_EDGE) {
            splitEdges.add(firstAndLastEdge, firstTypeSubstractedEdge);
        }
        splitEdges.add(firstAndLastEdge, newEdge);

        final IEdge lastTypeSubstractedEdge =
            IEdge.create(lastEdge.from, lastEdge.fromPos, lastEdge.to,
                lastEdge.type.subtractType(colapsedEdgeType));


        boolean deleteLast = false;
        if (maybeDeleteLast) {
            ITerm<?> possibleStartTerm = graph.getTerm(lastEdge.from);
            for (IPosition pos : possibleStartTerm.getPositions()) {
                ITerm<?> subTerm = possibleStartTerm.getSubterm(pos);

                if (pos.isEmptyPosition()) {
                    if (!subTerm.isVariable()) {
                        IFunctionSymbol<?> root = ((IFunctionApplication<?>) subTerm).getRootSymbol();
                        if (!graph.getDefinedSymbols().contains(root) && !root.isPredefinedFunction()) {
                            deleteLast = true;
                            newEdgeConditions.putFalse(lastEdge);
                            break;
                        }
                    }
                } else {
                    if (!subTerm.isVariable()) {
                        IFunctionSymbol<?> root = ((IFunctionApplication<?>) subTerm).getRootSymbol();
                        if (graph.getDefinedSymbols().contains(root) || root.isPredefinedFunction()) {
                            deleteLast = true;
                            newEdgeConditions.putFalse(lastEdge);
                            break;
                        }
                    }
                }
            }
        }

        if (!deleteLast) {
            splitEdges.add(firstAndLastEdge, lastEdge);
        }

        newEdgeConditions.putOr(lastTypeSubstractedEdge,
            graph.getCondition(lastEdge));
        if (lastTypeSubstractedEdge.type != EdgeType.NO_EDGE) {
            splitEdges.add(firstAndLastEdge, lastTypeSubstractedEdge);
        }

        return newEdge;
    }

    public static class Arguments {
        public int collapseSSelfLoops = 0;
    }

    protected static class CIdtPathCollapseProof extends DefaultProof {

        private final List<CIdtCollapsedPathsResult> collapsResult;

        public CIdtPathCollapseProof(List<CIdtCollapsedPathsResult> collapsResult) {
            this.collapsResult = collapsResult;
        }

        @Override
        public String export(Export_Util eu, VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("old edges / new edges:");
            sb.append(eu.linebreak());
            sb.append(eu.linebreak());
            for (CIdtCollapsedPathsResult res : this.collapsResult) {
                for (Entry<Pair<IEdge, IEdge>, ImmutableSet<IEdge>> entry :  res.edgeSplit.entrySet()) {
                    sb.append("[" + entry.getKey().x + ", " + entry.getKey().y + "]" + eu.appSpace() + " / " + eu.appSpace() + entry.getValue());
                    sb.append(eu.linebreak());
                    sb.append(eu.linebreak());
                }
                sb.append(eu.linebreak());
            }

            sb.append(eu.linebreak());
            sb.append(eu.linebreak());
            sb.append("collapsed self loops / times:");
            sb.append(eu.linebreak());
            sb.append(eu.linebreak());
            for (CIdtCollapsedPathsResult res : this.collapsResult) {
                for (Map.Entry<IEdge, Integer> entry :  res.collapsedSelfLoops.entrySet()) {
                    sb.append(entry.getKey() + eu.appSpace() + " / " + eu.appSpace() + entry.getValue());
                    sb.append(eu.linebreak());
                    sb.append(eu.linebreak());
                }
            }
            return sb.toString();
        }

    }
}
