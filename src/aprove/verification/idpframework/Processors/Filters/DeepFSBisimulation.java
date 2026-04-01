package aprove.verification.idpframework.Processors.Filters;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.bisimulation.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.Filters.Bisimulation.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * @author Marc Brockschmidt
 */
public class DeepFSBisimulation extends AbstractIDPFilter<Result, TIDPProblem> {

    private static final IPosition FALSE_Position = IPosition.create(new int[] {0 });
    private static final IPosition TRUE_Position = IPosition.create(new int[] {1 });

    private static final IPosition IMPLICATION_PRECONDITION = DeepFSBisimulation.FALSE_Position;
    private static final IPosition IMPLICATION_CONCLUSION = DeepFSBisimulation.TRUE_Position;

    private static final IPosition NODE_CONDITION = DeepFSBisimulation.TRUE_Position;
    private static final IPosition EDGE_CONDITION = DeepFSBisimulation.TRUE_Position;

    public DeepFSBisimulation() {
        super("DeepFSBisimulation", FilterMode.REMOVE_FILTERED_ATOMS);
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return false;
    }

    @Override
    protected Result processIDPProblem(final TIDPProblem idp, final Abortion aborter) throws AbortionException {
        final Triple<FilterReplacement, Set<Set<INode>>, VarRenaming> filter = DeepFSBisimulation.createFilter(idp, aborter);

        //        boolean isMeltingNodes = false;
        //        for (final Set<INode> nodeEqClass : filter.y) {
        //            if (nodeEqClass.size() > 1) {
        //                isMeltingNodes = true;
        //                break;
        //            }
        //        }

        final TIDPProblem intermediateIDP = this.createNewIDP(idp, filter.x, aborter);

        final IDPProblem newIDP = this.meltNodes(intermediateIDP, filter.y, filter.z);

        if (newIDP != idp) {
            return ResultFactory.proved(newIDP, YNMImplication.EQUIVALENT, new DeepFsBisimulationProof(
                filter.x,
                filter.z));
        }
        return ResultFactory.unsuccessful();
    }

    private TIDPProblem meltNodes(
        final TIDPProblem idp,
        final Set<Set<INode>> nodeEqClasses,
        final VarRenaming varUnification)
    {

        final IDependencyGraph idpGraph = idp.getIdpGraph();

        final Map<INode, INode> nodeSubstitutions = this.createNodeSubstitutions(idpGraph.getNodes(), nodeEqClasses);

        final NodeConditionMap newNodeConditions =
            new NodeConditionMap(idpGraph.getItpfFactory(), idpGraph.getFreshVarGenerator());
        final EdgeConditionMap newEdgeConditions =
            new EdgeConditionMap(idpGraph.getItpfFactory(), idpGraph.getFreshVarGenerator());

        final Set<INode> newInitialRewriteNodes = new LinkedHashSet<INode>();
        final Map<INode, Integer> nodeUnrollCounter = new LinkedHashMap<INode, Integer>();

        final List<LinkedHashSet<IEdge>> newSubGraphs = new ArrayList<LinkedHashSet<IEdge>>();
        for (final IDPSubGraph subGraph : idp.getSubGraphs()) {
            newSubGraphs.add(new LinkedHashSet<IEdge>(subGraph.getEdges()));
        }

        for (final Map.Entry<INode, INode> nodeSubstitution : nodeSubstitutions.entrySet()) {

            final INode node = nodeSubstitution.getKey();
            final INode replacedBy = nodeSubstitution.getValue();

            if (idpGraph.isInitialRewriteNode(node)) {
                newInitialRewriteNodes.add(replacedBy);
            }

            final Integer nodeUnrolls = idpGraph.getNodeUnrollCounter().get(node);
            final Integer oldUnroll = nodeUnrollCounter.put(replacedBy, nodeUnrolls);
            if (oldUnroll != null && oldUnroll > nodeUnrolls) {
                nodeUnrollCounter.put(replacedBy, oldUnroll);
            }

            newNodeConditions.putOr(replacedBy, idpGraph.getCondition(node));

            final ImmutableMap<INode, ImmutableSet<IEdge>> nodeSuccEdges = idpGraph.getSuccessors(node);

            for (final ImmutableSet<IEdge> succEdges : nodeSuccEdges.values()) {
                for (final IEdge succEdge : succEdges) {
                    final INode replacedTo = nodeSubstitutions.get(succEdge.to);
                    final IEdge newEdge = IEdge.create(replacedBy, succEdge.fromPos, replacedTo, succEdge.type);
                    final Itpf newCondition = idpGraph.getCondition(succEdge).applySubstitution(varUnification, true);
                    newEdgeConditions.putOr(newEdge, newCondition);
                    for (final LinkedHashSet<IEdge> subGraph : newSubGraphs) {
                        if (subGraph.remove(succEdge)) {
                            subGraph.add(newEdge);
                        }
                    }
                }
            }
        }

        final LinkedHashMap<INode, ITerm<?>> newNodeTerms = new LinkedHashMap<INode, ITerm<?>>();
        final Map<INode, VarRenaming> newLoopRenamings = new LinkedHashMap<INode, VarRenaming>();
        final Set<IVariable<?>> freeVars = new LinkedHashSet<IVariable<?>>();

        for (final INode node : newNodeConditions.keySet()) {
            final ITerm<?> newTerm = idpGraph.getTerm(node).applySubstitution(varUnification);
            newNodeTerms.put(node, newTerm);
            newTerm.collectVariables(freeVars);

            final VarRenaming loopRenaming = idpGraph.getLoopRenaming(node);
            final LinkedHashMap<IVariable<?>, IVariable<?>> newLoopRenaming =
                new LinkedHashMap<IVariable<?>, IVariable<?>>();
            for (final Map.Entry<? extends IVariable<?>, ? extends IVariable<?>> subst : loopRenaming
                .getMap()
                .entrySet())
            {
                final IVariable<?> toVar = subst.getValue().applyVarSubstitution(varUnification);
                newLoopRenaming.put(subst.getKey().applyVarSubstitution(varUnification), toVar);
                freeVars.add(toVar);
            }
            assert newLoopRenaming.keySet().containsAll(newTerm.getVariables()) : "var subst bad";

            newLoopRenamings.put(
                node,
                VarRenaming.create(ImmutableCreator.create(newLoopRenaming), false, idp.getPolyFactory()));
        }

        for (final Map.Entry<IEdge, Itpf> edgeCondition : newEdgeConditions.entrySet()) {
            edgeCondition.setValue(this.cleanQuantification(idpGraph.getItpfFactory(), edgeCondition.getValue(), freeVars));
        }

        if (newNodeConditions.isEmpty() || newEdgeConditions.isEmpty()) {
            return idp;
        }

        final IDependencyGraph newIdpGraph =
            IDependencyGraph.create(
                idp.getPredefinedMap(),
                idp.getIdpGraph().getQ(),
                idp.getItpfFactory(),
                idp.getPolyInterpretation(),
                ImmutableCreator.create(newNodeTerms),
                ImmutableCreator.create(newNodeConditions.getMap()),
                ImmutableCreator.create(newInitialRewriteNodes),
                ImmutableCreator.create(nodeUnrollCounter),
                ImmutableCreator.create(newLoopRenamings),
                ImmutableCreator.create(newEdgeConditions.getMap()),
                idp.getIdpGraph().getFreshVarGenerator());

        final LinkedHashSet<IDPSubGraph> immutableSubGraphs = new LinkedHashSet<IDPSubGraph>();
        for (final LinkedHashSet<IEdge> subGraph : newSubGraphs) {
            immutableSubGraphs.add(new IDPSubGraph(ImmutableCreator.create(subGraph)));
        }

        return idp.change(newIdpGraph, ImmutableCreator.create(GraphUtil.cleanupSubGraphs(immutableSubGraphs)));
    }

    private
        Itpf
        cleanQuantification(final ItpfFactory itpfFactory, final Itpf formula, final Set<IVariable<?>> freeVars)
    {
        final ImmutableList<ItpfQuantor> formulaQuantification = formula.getQuantification();

        final ArrayList<ItpfQuantor> newQuantors = new ArrayList<ItpfQuantor>(formulaQuantification.size());
        boolean changed = false;
        for (final ItpfQuantor quantor : formulaQuantification) {
            final IVariable<?> var = quantor.getVariable();
            if (freeVars.contains(var)) {
                changed = true;
            } else {
                newQuantors.add(quantor);
            }
        }

        if (changed) {
            return itpfFactory.create(ImmutableCreator.create(newQuantors), formula.getClauses());
        } else {
            return formula;
        }
    }

    private Map<INode, INode> createNodeSubstitutions(
        final ImmutableSet<INode> nodes,
        final Set<Set<INode>> nodeEqClasses)
    {
        final Map<INode, INode> nodeSubstitutions = new LinkedHashMap<INode, INode>();

        for (final Set<INode> nodeEqClass : nodeEqClasses) {
            final Iterator<INode> nodeIterator = nodeEqClass.iterator();
            final INode representative = nodeIterator.next();
            nodeSubstitutions.put(representative, representative);

            while (nodeIterator.hasNext()) {
                final INode node = nodeIterator.next();
                nodeSubstitutions.put(node, representative);
            }
        }

        for (final INode node : nodes) {
            if (!nodeSubstitutions.containsKey(node)) {
                nodeSubstitutions.put(node, node);
            }
        }
        return nodeSubstitutions;
    }

    @Override
    public boolean isIDPApplicable(final IDPProblem idp) {
        return true;
    }

    public static Triple<FilterReplacement, Set<Set<INode>>, VarRenaming> createFilter(
        final IDPProblem idp,
        final Abortion aborter) throws AbortionException
    {
        final SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>> graph = DeepFSBisimulation.createGraph(idp);

        if (graph.getNodes().isEmpty()) {
            return null;
        }
        final Collection<Set<Node<BisimObject>>> initialPartition =
            DeepFSBisimulation.getInitialPartition(idp.getIdpGraph(), graph, idp.getPredefinedMap());

        final IBisimulationAlgorithm<BisimObject, Pair<IPosition, EdgeType>> bisimAlg =
            new PartitionSplittingBisimulation<BisimObject, Pair<IPosition, EdgeType>>();
        final Collection<Set<Node<BisimObject>>> bisim = bisimAlg.getBisimulation(graph, initialPartition, aborter);

        final FunctionSymbolReplacement fsReplacement = new FunctionSymbolReplacement();
        final Set<Set<INode>> nodeEqClasses = new LinkedHashSet<Set<INode>>();
        final Map<IVariable<?>, IVariable<?>> varUnification = new LinkedHashMap<IVariable<?>, IVariable<?>>();

        for (final Set<Node<BisimObject>> eqClass : bisim) {
            final LinkedHashSet<IFunctionSymbol<?>> fsEqClass = new LinkedHashSet<IFunctionSymbol<?>>();
            final LinkedHashSet<INode> nodeEqClass = new LinkedHashSet<INode>();
            final LinkedHashSet<IVariable<?>> varEqClass = new LinkedHashSet<IVariable<?>>();

            for (final Node<BisimObject> n : eqClass) {
                if (n.getObject() instanceof BisimINode) {
                    final INode node = ((BisimINode) n.getObject()).getNode();
                    nodeEqClass.add(node);
                    assert (fsEqClass.size() == 0) : "node and function symbol bisimilar!";
                    assert (varEqClass.size() == 0) : "variable and node bisimilar!";
                } else if (n.getObject() instanceof BisimFS) {
                    final IFunctionSymbol<?> fs = ((BisimFS) n.getObject()).getFs();
                    if (!PredefinedUtil.isPredefined(fs)) {
                        fsEqClass.add(fs);
                    }
                    assert (nodeEqClass.size() == 0) : "node and function symbol bisimilar!";
                    assert (varEqClass.size() == 0) : "variable and function symbol bisimilar!";
                } else if (n.getObject() instanceof BisimTerm) {
                    final BisimTerm bisimTerm = ((BisimTerm) n.getObject());
                    if (bisimTerm.getTerm().isVariable()) {
                        varEqClass.add((IVariable<?>) bisimTerm.getTerm());

                        assert (fsEqClass.size() == 0) : "variable and function symbol bisimilar!";
                        assert (nodeEqClass.size() == 0) : "variable and node bisimilar!";
                    }
                }
            }

            if (fsEqClass.size() > 1) {
                DeepFSBisimulation.addEqClassToFsReplacement(fsReplacement, fsEqClass);
            }

            if (nodeEqClass.size() >= 1) {
                nodeEqClasses.add(nodeEqClass);
            }

            if (varEqClass.size() > 1) {
                DeepFSBisimulation.addEqClassToVarUnification(varUnification, varEqClass);
            }
        }

        final FilterReplacement filter = new FilterReplacement(fsReplacement, VarRenaming.EMPTY_RENAMING);

        return new Triple<FilterReplacement, Set<Set<INode>>, VarRenaming>(filter, nodeEqClasses, VarRenaming.create(
            ImmutableCreator.create(varUnification),
            true,
            idp.getPolyFactory()));
    }

    private static void addEqClassToVarUnification(
        final Map<IVariable<?>, IVariable<?>> varUnification,
        final LinkedHashSet<IVariable<?>> varEqClass)
    {
        final Iterator<IVariable<?>> varIterator = varEqClass.iterator();
        final IVariable<?> representative = varIterator.next();

        while (varIterator.hasNext()) {
            final IVariable<?> var = varIterator.next();
            varUnification.put(var, representative);
        }
    }

    private static void addEqClassToFsReplacement(
        final FunctionSymbolReplacement fsReplacement,
        final Collection<IFunctionSymbol<?>> fsEqClass)
    {
        final Iterator<IFunctionSymbol<?>> fsIterator = fsEqClass.iterator();
        final IFunctionSymbol<?> representative = fsIterator.next();
        final ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>> replacedBy =
            new ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>>(
                representative,
                FunctionSymbolReplacement.createRetainAllPositions(representative));

        while (fsIterator.hasNext()) {
            final IFunctionSymbol<?> fs = fsIterator.next();
            fsReplacement.put(fs, replacedBy);
        }
    }

    /**
     * @param graph the graph describing the rewrite relation and subterm
     * connections.
     * @return partition for our bisimulation, where function symbols are in one
     * class per arity, all variables are in one class and all nodes are in one
     * class.
     */
    @SuppressWarnings("unchecked")
    private static Collection<Set<Node<BisimObject>>> getInitialPartition(
        final IDependencyGraph idpGraph,
        final SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>> graph,
        final IDPPredefinedMap idpPredefinedMap)
    {
        final CollectionMap<Class<?>, Node<BisimObject>> partitioning =
            new CollectionMap<Class<?>, Node<BisimObject>>();

        final CollectionMap<Integer, Node<BisimObject>> definedFunctionSymbolClasses =
            new CollectionMap<Integer, Node<BisimObject>>();

        final Collection<Set<Node<BisimObject>>> res = new ArrayList<Set<Node<BisimObject>>>();

        for (final Node<BisimObject> node : graph.getNodes()) {
            if (node.getObject() instanceof BisimFS) {
                final BisimFS bisimFS = (BisimFS) node.getObject();
                final IFunctionSymbol<?> fs = bisimFS.getFs();
                if (fs.getSemantics() != null || idpGraph.isConstructor(fs)) {
                    res.add(Collections.singleton(node));
                } else {
                    definedFunctionSymbolClasses.add(fs.getArity(), node);
                }
            } else {
                partitioning.add(node.getObject().getClass(), node);
            }
        }

        res.addAll((Collection) partitioning.values());
        res.addAll((Collection) definedFunctionSymbolClasses.values());
        return res;
    }

    /**
     * Add a new connection to the graph, taking care of all caching, node and
     * edge label creation issues. The edge type is flattened to rewrite and inf
     * @param graph the graph in which we add the connection
     * @param elementToNodeMap map representing the node cache
     * @param t1 source of the edge
     * @param p edge label to add
     * @param edgeType type of the edge
     * @param t2 target of the edge
     */
    private static void addConnection(
        final SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>> graph,
        final LinkedHashMap<BisimObject, Node<BisimObject>> elementToNodeMap,
        final Node<BisimObject> n1,
        final IPosition p,
        final EdgeType edgeType,
        final Node<BisimObject> n2)
    {

        Set<Pair<IPosition, EdgeType>> edgeLabel;
        if (graph.contains(n1, n2)) {
            edgeLabel = graph.removeEdgeAndReturnLabel(n1, n2);
        } else {
            edgeLabel = new LinkedHashSet<Pair<IPosition, EdgeType>>();
        }

        if (edgeType == null) {
            edgeLabel.add(new Pair<IPosition, EdgeType>(p, edgeType));
        } else {
            EdgeType combined = EdgeType.NO_EDGE;
            if (edgeType.isInf()) {
                edgeLabel.add(new Pair<IPosition, EdgeType>(p, EdgeType.INF));
                combined = combined.addType(EdgeType.INF);
            }

            if (edgeType.isRewrite()) {
                edgeLabel.add(new Pair<IPosition, EdgeType>(p, EdgeType.REWRITE));
                combined = combined.addType(EdgeType.REWRITE);
            }

            assert combined.equals(edgeType) : "given edge type is not properly represented";
        }

        graph.addEdge(n1, n2, edgeLabel);
    }

    /**
     * @param e some element
     * @param graph the graph in which we store the nodes;
     * @param elementToNodeMap map representing the node cache
     * @return the cached node for <code>e</code> or a new node which is now
     * also stored in the graph and cache.
     */
    private static Node<BisimObject> createNode(
        final BisimObject e,
        final SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>> graph,
        final LinkedHashMap<BisimObject, Node<BisimObject>> elementToNodeMap)
    {
        final Node<BisimObject> newNode = new Node<BisimObject>(e);
        elementToNodeMap.put(e, newNode);
        graph.addNode(newNode);
        return newNode;
    }

    /**
     * Add connections to subterm symbols to the graph (for all subterms).
     * @param graph the graph in which we add the connections
     * @param elementToNodeMap map representing the node cache
     * @param fsToRulesMap map from function symbols to nodes representing their rules
     * @param t some ITerm
     * @return
     */
    private static Node<BisimObject> addTermNode(
        final SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>> graph,
        final LinkedHashMap<BisimObject, Node<BisimObject>> elementToNodeMap,
        final Map<IFunctionSymbol<?>, Collection<Triple<Node<BisimObject>, IPosition, EdgeType>>> fsToRulesMap,
        final ITerm<?> t)
    {

        final BisimTerm bisimT = new BisimTerm(t);

        if (elementToNodeMap.containsKey(bisimT)) {
            final Node<BisimObject> node = elementToNodeMap.get(bisimT);
            return node;
        }

        final Node<BisimObject> node = DeepFSBisimulation.createNode(bisimT, graph, elementToNodeMap);
        if (!t.isVariable()) {
            final IFunctionApplication<?> fa = (IFunctionApplication<?>) t;
            final IFunctionSymbol<?> fs = fa.getRootSymbol();
            final Node<BisimObject> fsNode = DeepFSBisimulation.addFSNode(graph, elementToNodeMap, fsToRulesMap, fs);
            DeepFSBisimulation.addConnection(graph, elementToNodeMap, node, IPosition.EMPTY, null, fsNode);

            final ImmutableArrayList<ITerm<?>> arguments = fa.getArguments();
            for (int i = arguments.size() - 1; i >= 0; i--) {
                final ITerm<?> arg = arguments.get(i);
                final Node<BisimObject> argNode = DeepFSBisimulation.addTermNode(graph, elementToNodeMap, fsToRulesMap, arg);
                final IPosition position = IPosition.create(new int[] {i });
                DeepFSBisimulation.addConnection(graph, elementToNodeMap, node, position, null, argNode);
                if (arg.isVariable()) {
                    DeepFSBisimulation.addConnection(graph, elementToNodeMap, argNode, position, null, node);
                } else {
                    final IFunctionApplication<?> argFa = (IFunctionApplication<?>) arg;
                    final Collection<Triple<Node<BisimObject>, IPosition, EdgeType>> rules =
                        fsToRulesMap.get(argFa.getRootSymbol());
                    if (rules == null || rules.isEmpty()) {
                        DeepFSBisimulation.addConnection(graph, elementToNodeMap, argNode, position, null, node);
                    }
                }
            }
        }

        return node;
    }

    private static Node<BisimObject> addFSNode(
        final SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>> graph,
        final LinkedHashMap<BisimObject, Node<BisimObject>> elementToNodeMap,
        final Map<IFunctionSymbol<?>, Collection<Triple<Node<BisimObject>, IPosition, EdgeType>>> fsToRulesMap,
        final IFunctionSymbol<?> fs)
    {
        final BisimFS bisimFS = new BisimFS(fs);

        if (elementToNodeMap.containsKey(bisimFS)) {
            final Node<BisimObject> node = elementToNodeMap.get(bisimFS);
            return node;
        }

        final Node<BisimObject> node = DeepFSBisimulation.createNode(bisimFS, graph, elementToNodeMap);
        final Collection<Triple<Node<BisimObject>, IPosition, EdgeType>> ruleNodes = fsToRulesMap.get(fs);

        if (ruleNodes != null) {
            for (final Triple<Node<BisimObject>, IPosition, EdgeType> ruleDescriptor : ruleNodes) {
                final Node<BisimObject> ruleNode = ruleDescriptor.x;
                assert ruleNode.getObject() instanceof BisimINode;
                DeepFSBisimulation.addConnection(graph, elementToNodeMap, node, ruleDescriptor.y, ruleDescriptor.z, ruleNode);
            }
        }

        return node;
    }

    private static Node<BisimObject> addItpfNode(
        final SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>> graph,
        final LinkedHashMap<BisimObject, Node<BisimObject>> elementToNodeMap,
        final Map<IFunctionSymbol<?>, Collection<Triple<Node<BisimObject>, IPosition, EdgeType>>> fsToRulesMap,
        final IDPPredefinedMap predefinedMap,
        final ItpfFactory itpfFactory,
        final Itpf formula)
    {

        final BisimItpf bisimFormula = new BisimItpf(formula);

        if (elementToNodeMap.containsKey(bisimFormula)) {
            final Node<BisimObject> node = elementToNodeMap.get(bisimFormula);
            return node;
        }

        final Node<BisimObject> node = DeepFSBisimulation.createNode(bisimFormula, graph, elementToNodeMap);

        if (!formula.getQuantification().isEmpty()) {
            final ImmutableList<ItpfQuantor> quantification = formula.getQuantification();
            boolean currentQuantorType = quantification.get(0).isUniversalQuantor();
            IPosition currentPosition =
                currentQuantorType ? IPosition.create(new int[] {1 }) : IPosition.create(new int[] {0 });
            for (final ItpfQuantor quantor : formula.getQuantification()) {
                if (quantor.isUniversalQuantor() != currentQuantorType) {
                    currentQuantorType = quantor.isUniversalQuantor();
                    currentPosition = currentQuantorType ? currentPosition.append(1) : currentPosition.append(0);
                }
                final Node<BisimObject> varNode =
                    DeepFSBisimulation.addTermNode(graph, elementToNodeMap, fsToRulesMap, quantor.getVariable());
                DeepFSBisimulation.addConnection(graph, elementToNodeMap, node, currentPosition, null, varNode);
                DeepFSBisimulation.addConnection(graph, elementToNodeMap, varNode, currentPosition, null, node);
            }
        }

        for (final ItpfConjClause clause : formula.getClauses()) {
            final Node<BisimObject> clauseNode =
                DeepFSBisimulation.addConjClauseNode(graph, elementToNodeMap, fsToRulesMap, predefinedMap, itpfFactory, clause);
            DeepFSBisimulation.addConnection(graph, elementToNodeMap, node, IPosition.EMPTY, null, clauseNode);
        }

        return node;
    }

    private static Node<BisimObject> addConjClauseNode(
        final SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>> graph,
        final LinkedHashMap<BisimObject, Node<BisimObject>> elementToNodeMap,
        final Map<IFunctionSymbol<?>, Collection<Triple<Node<BisimObject>, IPosition, EdgeType>>> fsToRulesMap,
        final IDPPredefinedMap predefinedMap,
        final ItpfFactory itpfFactory,
        final ItpfConjClause clause)
    {
        final BisimConjClause bisimClause = new BisimConjClause(clause);

        if (elementToNodeMap.containsKey(bisimClause)) {
            final Node<BisimObject> node = elementToNodeMap.get(bisimClause);
            return node;
        }

        final Node<BisimObject> node = DeepFSBisimulation.createNode(bisimClause, graph, elementToNodeMap);

        for (final Map.Entry<? extends ItpfAtom, Boolean> literal : clause.getLiterals().entrySet()) {
            final IPosition position = literal.getValue() ? DeepFSBisimulation.TRUE_Position : DeepFSBisimulation.FALSE_Position;
            final ItpfAtom atom = literal.getKey();
            Node<BisimObject> atomNode;
            if (atom.isItp()) {
                atomNode = DeepFSBisimulation.addItpNode(graph, elementToNodeMap, fsToRulesMap, (ItpfItp) atom);
            } else if (atom.isPoly()) {
                atomNode =
                    DeepFSBisimulation.addPolyNode(
                        graph,
                        elementToNodeMap,
                        fsToRulesMap,
                        predefinedMap,
                        itpfFactory,
                        (ItpfPolyAtom<?>) atom);
            } else if (atom.isImplication()) {
                atomNode =
                    DeepFSBisimulation.addImplicationNode(
                        graph,
                        elementToNodeMap,
                        fsToRulesMap,
                        predefinedMap,
                        itpfFactory,
                        (ItpfImplication) atom);
            } else {
                throw new UnsupportedOperationException("unsupported atom type");
            }

            DeepFSBisimulation.addConnection(graph, elementToNodeMap, node, position, null, atomNode);
        }

        return node;
    }

    private static Node<BisimObject> addImplicationNode(
        final SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>> graph,
        final LinkedHashMap<BisimObject, Node<BisimObject>> elementToNodeMap,
        final Map<IFunctionSymbol<?>, Collection<Triple<Node<BisimObject>, IPosition, EdgeType>>> fsToRulesMap,
        final IDPPredefinedMap predefinedMap,
        final ItpfFactory itpfFactory,
        final ItpfImplication implication)
    {
        final BisimImplication bisimImplication = new BisimImplication(implication);

        if (elementToNodeMap.containsKey(bisimImplication)) {
            final Node<BisimObject> node = elementToNodeMap.get(bisimImplication);
            return node;
        }

        final Node<BisimObject> node = DeepFSBisimulation.createNode(bisimImplication, graph, elementToNodeMap);

        final Node<BisimObject> preconditionNode =
            DeepFSBisimulation.addItpfNode(
                graph,
                elementToNodeMap,
                fsToRulesMap,
                predefinedMap,
                itpfFactory,
                implication.getPrecondition());

        DeepFSBisimulation.addConnection(graph, elementToNodeMap, node, DeepFSBisimulation.IMPLICATION_PRECONDITION, null, preconditionNode);

        final Node<BisimObject> conclusionNode =
            DeepFSBisimulation.addItpfNode(graph, elementToNodeMap, fsToRulesMap, predefinedMap, itpfFactory, implication.getConclusion());
        DeepFSBisimulation.addConnection(graph, elementToNodeMap, node, DeepFSBisimulation.IMPLICATION_CONCLUSION, null, conclusionNode);

        return node;
    }

    private static Node<BisimObject> addItpNode(
        final SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>> graph,
        final LinkedHashMap<BisimObject, Node<BisimObject>> elementToNodeMap,
        final Map<IFunctionSymbol<?>, Collection<Triple<Node<BisimObject>, IPosition, EdgeType>>> fsToRulesMap,
        final ItpfItp itp)
    {
        final BisimItp bisimItp = new BisimItp(itp);

        if (elementToNodeMap.containsKey(bisimItp)) {
            final Node<BisimObject> node = elementToNodeMap.get(bisimItp);
            return node;
        }

        final Node<BisimObject> node = DeepFSBisimulation.createNode(bisimItp, graph, elementToNodeMap);

        assert itp.canIgnoreContextL() && itp.canIgnoreContextR() : "context is not suppoerted";

        final Node<BisimObject> lNode = DeepFSBisimulation.addTermNode(graph, elementToNodeMap, fsToRulesMap, itp.getL());
        final Node<BisimObject> rNode = DeepFSBisimulation.addTermNode(graph, elementToNodeMap, fsToRulesMap, itp.getR());

        final int relationOrdinal = itp.getRelation().ordinal();

        final IPosition lPosition = IPosition.create(new int[] {relationOrdinal, 0 });
        IPosition rPosition;
        if (itp.getRelation() == ItpRelation.EQ) {
            rPosition = lPosition;
        } else {
            rPosition = IPosition.create(new int[] {relationOrdinal, 1 });
        }

        DeepFSBisimulation.addConnection(graph, elementToNodeMap, node, lPosition, null, lNode);
        DeepFSBisimulation.addConnection(graph, elementToNodeMap, node, rPosition, null, rNode);

        DeepFSBisimulation.addConnection(graph, elementToNodeMap, rNode, IPosition.EMPTY, null, node);

        return node;
    }

    private static Node<BisimObject> addPolyNode(
        final SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>> graph,
        final LinkedHashMap<BisimObject, Node<BisimObject>> elementToNodeMap,
        final Map<IFunctionSymbol<?>, Collection<Triple<Node<BisimObject>, IPosition, EdgeType>>> fsToRulesMap,
        final IDPPredefinedMap predefinedMap,
        final ItpfFactory itpfFactory,
        final ItpfPolyAtom<?> atom)
    {
        final SemiRingDomain<?> dom = atom.getPoly().getDomain();
        final List<SemiRingDomain<?>> dom_dom = new ArrayList<SemiRingDomain<?>>(2);
        dom_dom.add(dom);
        dom_dom.add(dom);

        final IFunctionSymbol<?> constraintSym =
            predefinedMap.getFunctionSymbol(atom.getConstraintType().getFunction(), dom_dom);
        final ITerm<?> polyTerm = atom.getPoly().toTerm(predefinedMap);
        final ITerm<?> zeroTerm = atom.getPoly().getRing().zero().getTerm(predefinedMap);
        final PfBoolean trueTerm = predefinedMap.getBoolean(true);
        final IFunctionApplication<?> leftTerm = IFunctionApplication.create(constraintSym, polyTerm, zeroTerm);

        final ItpfItp itp =
            itpfFactory.createItp(leftTerm, null, null, ItpRelation.TO_TRANS, trueTerm.getTerm(), null, null);

        return DeepFSBisimulation.addItpNode(graph, elementToNodeMap, fsToRulesMap, itp);
    }

    /**
     * Create the initial graph, where nodes are all iNodes, function symbols
     * and variables occurring in the system. Edges are connecting function
     * symbols to occurring subterms (i.e. the symbols or variables there),
     * where the edge label contains the IPosition that connects the two. iEdges
     * are represented with edges from the from-node to the to-node and labeled
     * by the from-position. ITPs are represented with edges from the lhs root
     * symbol / variable to the rhs root symbol/variable and labeled by the
     * empty IPosition.
     * @param idp The rule system for our bisimulation.
     * @return a graph suitable for deep function symbol bisimulation.
     */
    private static SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>> createGraph(final IDPProblem idp) {
        final SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>> graph =
            new SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>>();

        final LinkedHashMap<BisimObject, Node<BisimObject>> elementToNodeMap =
            new LinkedHashMap<BisimObject, Node<BisimObject>>();

        final LinkedHashMap<INode, Node<BisimObject>> nodeToNodeMap = DeepFSBisimulation.createGraphNodes(graph, elementToNodeMap, idp);

        final Map<IFunctionSymbol<?>, Collection<Triple<Node<BisimObject>, IPosition, EdgeType>>> fsToRulesMap =
            DeepFSBisimulation.createFsToNodeMap(graph, elementToNodeMap, nodeToNodeMap, idp);

        DeepFSBisimulation.createNodeEdges(graph, elementToNodeMap, fsToRulesMap, nodeToNodeMap, idp);

        DeepFSBisimulation.convertEdges(graph, elementToNodeMap, fsToRulesMap, nodeToNodeMap, idp);

        return graph;
    }

    private static void createNodeEdges(
        final SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>> graph,
        final LinkedHashMap<BisimObject, Node<BisimObject>> elementToNodeMap,
        final Map<IFunctionSymbol<?>, Collection<Triple<Node<BisimObject>, IPosition, EdgeType>>> fsToRulesMap,
        final LinkedHashMap<INode, Node<BisimObject>> nodeToNodeMap,
        final IDPProblem idp)
    {
        final IDependencyGraph idpGraph = idp.getIdpGraph();
        final ItpfFactory itpfFactory = idpGraph.getItpfFactory();
        final IDPPredefinedMap predefinedMap = idpGraph.getPredefinedMap();

        for (final Map.Entry<INode, Node<BisimObject>> nodeToNode : nodeToNodeMap.entrySet()) {
            final Node<BisimObject> bisimNode = nodeToNode.getValue();
            final ITerm<?> term = idpGraph.getTerm(nodeToNode.getKey());
            final Node<BisimObject> termNode = DeepFSBisimulation.addTermNode(graph, elementToNodeMap, fsToRulesMap, term);
            DeepFSBisimulation.addConnection(graph, elementToNodeMap, bisimNode, IPosition.EMPTY, null, termNode);

            DeepFSBisimulation.addVarConnections(graph, elementToNodeMap, fsToRulesMap, bisimNode, term);

            final Node<BisimObject> nodeConditionNode =
                DeepFSBisimulation.addItpfNode(
                    graph,
                    elementToNodeMap,
                    fsToRulesMap,
                    predefinedMap,
                    itpfFactory,
                    idpGraph.getCondition(nodeToNode.getKey()));
            DeepFSBisimulation.addConnection(graph, elementToNodeMap, nodeToNode.getValue(), DeepFSBisimulation.NODE_CONDITION, null, nodeConditionNode);
        }
    }

    private static void addVarConnections(
        final SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>> graph,
        final LinkedHashMap<BisimObject, Node<BisimObject>> elementToNodeMap,
        final Map<IFunctionSymbol<?>, Collection<Triple<Node<BisimObject>, IPosition, EdgeType>>> fsToRulesMap,
        final Node<BisimObject> bisimNode,
        final ITerm<?> term)
    {
        for (final IVariable<?> var : term.getVariables()) {
            final Node<BisimObject> varNode = DeepFSBisimulation.addTermNode(graph, elementToNodeMap, fsToRulesMap, var);
            //            addConnection(graph, elementToNodeMap, bisimNode, null, null, varNode);
            DeepFSBisimulation.addConnection(graph, elementToNodeMap, varNode, IPosition.EMPTY, null, bisimNode);
        }
    }

    private static void convertEdges(
        final SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>> graph,
        final LinkedHashMap<BisimObject, Node<BisimObject>> elementToNodeMap,
        final Map<IFunctionSymbol<?>, Collection<Triple<Node<BisimObject>, IPosition, EdgeType>>> fsToRulesMap,
        final LinkedHashMap<INode, Node<BisimObject>> nodeToNodeMap,
        final IDPProblem idp)
    {
        final IDependencyGraph idpGraph = idp.getIdpGraph();
        final ItpfFactory itpfFactory = idpGraph.getItpfFactory();
        final IDPPredefinedMap predefinedMap = idpGraph.getPredefinedMap();

        for (final Map.Entry<IEdge, Itpf> edgeEntry : idpGraph.getEdgeConditions().entrySet()) {
            final IEdge edge = edgeEntry.getKey();
            final BisimIEdge bisimEdge = new BisimIEdge(edge);
            final Node<BisimObject> edgeNode = new Node<BisimObject>(bisimEdge);

            final Node<BisimObject> fromNode = nodeToNodeMap.get(edge.from);
            final Node<BisimObject> toNode = nodeToNodeMap.get(edge.to);

            DeepFSBisimulation.addConnection(graph, elementToNodeMap, edgeNode, edge.fromPos, edge.type, fromNode);
            DeepFSBisimulation.addConnection(graph, elementToNodeMap, edgeNode, null, edge.type, toNode);

            final Node<BisimObject> edgeCondNode =
                DeepFSBisimulation.addItpfNode(graph, elementToNodeMap, fsToRulesMap, predefinedMap, itpfFactory, edgeEntry.getValue());

            DeepFSBisimulation.addConnection(graph, elementToNodeMap, edgeNode, DeepFSBisimulation.EDGE_CONDITION, null, edgeCondNode);
        }
    }

    private static
        Map<IFunctionSymbol<?>, Collection<Triple<Node<BisimObject>, IPosition, EdgeType>>>
        createFsToNodeMap(
            final SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>> graph,
            final LinkedHashMap<BisimObject, Node<BisimObject>> elementToNodeMap,
            final LinkedHashMap<INode, Node<BisimObject>> nodeToNodeMap,
            final IDPProblem idp)
    {
        final CollectionMap<IFunctionSymbol<?>, Triple<Node<BisimObject>, IPosition, EdgeType>> fsToNodeMap =
            new CollectionMap<IFunctionSymbol<?>, Triple<Node<BisimObject>, IPosition, EdgeType>>();

        final IDependencyGraph idpGraph = idp.getIdpGraph();
        for (final IEdge edge : idpGraph.getEdges()) {
            if (idpGraph.isInitialRewriteNode(edge.from)) {
                final ITerm<?> fromTerm = idpGraph.getTerm(edge.from).getSubterm(edge.fromPos);
                if (!fromTerm.isVariable()) {
                    final IFunctionApplication<?> fromFa = (IFunctionApplication<?>) fromTerm;
                    final IFunctionSymbol<?> rootFs = fromFa.getRootSymbol();

                    final Node<BisimObject> bisimFromNode = nodeToNodeMap.get(edge.from);
                    final Triple<Node<BisimObject>, IPosition, EdgeType> fsNode =
                        new Triple<Node<BisimObject>, IPosition, EdgeType>(
                            bisimFromNode,
                            new Pair<IPosition, EdgeType>(edge.fromPos, edge.type));

                    fsToNodeMap.add(rootFs, fsNode);
                } else {
                    throw new UnsupportedOperationException("edge originating from variable");
                }
            }
        }

        return fsToNodeMap;
    }

    private static LinkedHashMap<INode, Node<BisimObject>> createGraphNodes(
        final SimpleGraph<BisimObject, Set<Pair<IPosition, EdgeType>>> graph,
        final LinkedHashMap<BisimObject, Node<BisimObject>> elementToNodeMap,
        final IDPProblem idp)
    {
        final IDependencyGraph idpGraph = idp.getIdpGraph();

        final LinkedHashMap<INode, Node<BisimObject>> nodeToNode = new LinkedHashMap<INode, Node<BisimObject>>();

        for (final INode idpNode : idpGraph.getNodes()) {
            final BisimINode bisimIDPNode = new BisimINode(idpNode);
            final Node<BisimObject> node = new Node<BisimObject>(bisimIDPNode);
            graph.addNode(node);
            elementToNodeMap.put(bisimIDPNode, node);
            nodeToNode.put(idpNode, node);
        }

        return nodeToNode;
    }

    public static class DeepFsBisimulationProof extends AbstractFilterProof {

        private final VarRenaming varUnification;

        public DeepFsBisimulationProof(final FilterReplacement filter, final VarRenaming varUnification) {
            super(filter);
            this.varUnification = varUnification;
        }

        @Override
        public void export(final StringBuilder sb, final Export_Util o, final VerbosityLevel level) {
            super.export(sb, o, level);
            sb.append(o.newline());
            sb.append("Replaced variables:");
            sb.append(o.newline());
            this.varUnification.export(sb, o, level);
        }

    }

}
