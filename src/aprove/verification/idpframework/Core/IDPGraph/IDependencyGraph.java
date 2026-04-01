/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Core.IDPGraph;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Algorithms.Matching.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.FreshVarGenerator;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class IDependencyGraph implements Immutable,
        SelfMarkable<Singleton<IDependencyGraph>, IDependencyGraph>,
        IDPExportable,
        DOT_Able, ITermAnalysis<ITerm<?>> {

    /**
     * Integer constant representing the toDOT() method.
     */
    protected static final int DOT = 0;

    /**
     * Integer constant representing the toSaveDOT() method.
     */
    protected static final int SAVE = 1;

    /**
     * Integer constant representing the toSaveDOTwithEdges() method.
     */
    protected static final int EDGES = 2;

    /**
     * Integer constant representing the toInteractiveDOTwithEdges() method.
     */
    protected static final int INTERACTIVE = 3;

    /**
     * Integer constant representing the toDOTDOT() method.
     */
    protected static final int DOTDOT1 = 4;

    /**
     * Integer constant representing the toDOTDOT(boolean,float,float,boolean)
     * method.
     */
    protected static final int DOTDOT2 = 5;

    private static final int MAX_NODE_TERM_EXPORT_LENGTH = 80;

    public static ImmutableMap<INode, Integer> createEmptyNodeUnrollCounter(final Set<INode> nodes) {
        final Map<INode, Integer> counter = new LinkedHashMap<INode, Integer>();

        for (final INode node : nodes) {
            counter.put(node, 0);
        }

        return ImmutableCreator.create(counter);
    }

    public static IDependencyGraph create(final IDPPredefinedMap predefinedMap,
        final IQTermSet q,
        final ItpfFactory itpfFactory,
        final PolyInterpretation<?> polyInterpretation,
        final ImmutableMap<INode, ITerm<?>> nodes,
        final ImmutableMap<INode, Itpf> nodeConditions,
        final ImmutableSet<INode> initialRewriteNodes,
        final ImmutableMap<INode, Integer> nodeUnrollCounter,
        final ImmutableMap<INode, VarRenaming> loopRenamings,
        final ImmutableMap<IEdge, Itpf> edges,
        final FreshVarGenerator freshVarNameGenerator) {

        final ImmutableMap<IFunctionSymbol<?>, ImmutableSet<INode>> sortedInitialRewriteNodes =
            IDependencyGraph.sortInitialNodes(nodes, initialRewriteNodes);

        return IDependencyGraph.create(predefinedMap, q, itpfFactory, polyInterpretation,
            nodes, nodeConditions, sortedInitialRewriteNodes, nodeUnrollCounter,
            loopRenamings, edges, freshVarNameGenerator);
    }

    public static IDependencyGraph create(final IDPPredefinedMap predefinedMap,
        final IQTermSet q,
        final ItpfFactory itpfFactory,
        final PolyInterpretation<?> polyInterpretation,
        final ImmutableMap<INode, ITerm<?>> nodes,
        final ImmutableMap<INode, Itpf> nodeConditions,
        final ImmutableMap<IFunctionSymbol<?>, ImmutableSet<INode>> initialRewriteNodes,
        final ImmutableMap<INode, Integer> nodeUnrollCounter,
        final ImmutableMap<INode, VarRenaming> loopRenamings,
        final ImmutableMap<IEdge, Itpf> edges,
        final FreshVarGenerator freshVarNameGenerator) {
        final int maxNodeId =
            IDependencyGraph.assertGraphProperties(
                q,
                polyInterpretation,
                nodes,
                nodeUnrollCounter,
                loopRenamings,
                nodeConditions,
                initialRewriteNodes,
                edges,
                freshVarNameGenerator);

        return new IDependencyGraph(predefinedMap, itpfFactory, polyInterpretation, q, nodes,
            nodeConditions, initialRewriteNodes, nodeUnrollCounter, loopRenamings, edges, null, null, freshVarNameGenerator, maxNodeId);
    }

    private static int assertGraphProperties(final IQTermSet q,
        final PolyInterpretation<?> polyInterpretation,
        final Map<INode, ? extends ITerm<?>> nodes,
        final Map<INode, Integer> nodeUnrollCounter,
        final Map<INode, VarRenaming> loopRenamings,
        final Map<INode, Itpf> nodeConditions,
        final Map<IFunctionSymbol<?>, ImmutableSet<INode>> initialRewriteNodes,
        final Map<IEdge, Itpf> edges,
        final FreshVarGenerator freshVarNameGenerator) {
        final Set<IVariable<?>> usedVariables = new HashSet<IVariable<?>>();

        if (polyInterpretation != null) {
            final List<IVariable<?>> interpretedVars = new ArrayList<IVariable<?>>();
            for (final Map.Entry<IVariable<?>, ? extends IVariable<?>> varInterpretaTion : polyInterpretation.getVariableInterpretations().entrySet()) {
                if (!varInterpretaTion.getKey().equals(varInterpretaTion.getValue())) {
                    interpretedVars.add(varInterpretaTion.getValue());
                }
            }
            IDependencyGraph.assertUsedVariables(usedVariables, interpretedVars);
        }

        // checking nodes and node id
        int maxNodeId = -1;
        {
            final Set<Integer> usedNodeIds = new HashSet<Integer>();
            for (final Map.Entry<INode, ? extends ITerm<?>> entry : nodes.entrySet()) {
                assert usedNodeIds.add(entry.getKey().id) : "dupplicate node id";
                maxNodeId = Math.max(maxNodeId, entry.getKey().id);
            }
        }

        // loop unroll counter
        if (Globals.useAssertions) {
            assert nodeUnrollCounter.keySet().equals(nodes.keySet()) : "needs unroll counter for exactly all nodes";
        }

        // check loop substitutions
        if (Globals.useAssertions) {
            assert loopRenamings.keySet().containsAll(nodes.keySet());
            for (final Map.Entry<INode, VarRenaming> entry : loopRenamings.entrySet()) {
                final Set<IVariable<?>> nodeVars = nodes.get(entry.getKey()).getVariables();
                assert (entry.getValue().getMap().keySet().containsAll(nodeVars)) : "all variables must be renamed into fresh variables in loop substitution";
                final Set<IVariable<?>> image =
                    new HashSet<IVariable<?>>(entry.getValue().getMap().values());
//                assert image.size() == entry.getValue().getMap().size() : "a variable is renamed to itself";
//                image.retainAll(entry.getValue().getMap().keySet());
//                assert image.isEmpty() : "image variable is equal to source of loop substitution";
                IDependencyGraph.assertUsedVariables(usedVariables, entry.getValue().getTermDomain());
                IDependencyGraph.assertUsedVariables(usedVariables, entry.getValue().getTermVariablesInCodomain());
            }
        }

        // check node conditions
        if (Globals.useAssertions) {
            for (final Map.Entry<INode, Itpf> entry : nodeConditions.entrySet()) {
                final INode node = entry.getKey();
                final ITerm<?> fromTerm = nodes.get(node);
                final Set<IVariable<?>> variables =
                    new HashSet<IVariable<?>>(fromTerm.getVariables());
                assert variables.containsAll(entry.getValue().getFreeVariables()) : "unbound variable in condition is not matched by any term variable";

                IDependencyGraph.assertUsedVariables(usedVariables, entry.getValue().getBoundVariables());
            }
        }

        // check edges
        if (Globals.useAssertions) {
            for (final Map.Entry<IEdge, Itpf> entry : edges.entrySet()) {
                final IEdge edge = entry.getKey();
                assert (nodes.containsKey(edge.from)) : "edge: from node not contained in graph";
                assert (nodes.containsKey(edge.to)) : "edge: to node not contained in graph";
                final ITerm<?> fromTerm = nodes.get(edge.from);
                assert fromTerm.getLongestPrefixInTerm(edge.fromPos).equals(
                    edge.fromPos) : "edge: fromPos not legal";
                final Set<IVariable<?>> variables =
                    new HashSet<IVariable<?>>(fromTerm.getVariables());

                ITerm<?> toTerm;
                if (edge.to.equals(edge.from)) {
                    final VarRenaming renaming =
                        loopRenamings.get(edge.from);
                    assert renaming != null : "no loop renaming for node "
                        + edge.from;
                    toTerm = nodes.get(edge.to).applySubstitution(renaming);
                } else {
                    toTerm = nodes.get(edge.to);
                }
                variables.addAll(toTerm.getVariables());

                final Collection<IVariable<?>> interpretedVars = new ArrayList<IVariable<?>>(variables.size());
                if (polyInterpretation != null) {
                    final Map<IVariable<?>, ? extends IVariable<?>> varInterpretations = polyInterpretation.getVariableInterpretations();
                    for (final IVariable<?> var : variables) {
                        final IVariable<?> interpretedVar = varInterpretations.get(var);
                        if (interpretedVar != null) {
                            interpretedVars.add(interpretedVar);
                        }
                    }
                    variables.addAll(interpretedVars);
                }

                final ImmutableSet<IVariable<?>> freeVars = entry.getValue().getFreeVariables();

                for (final IVariable<?> freeVar : freeVars) {
                    assert variables.contains(freeVar) || (polyInterpretation != null && polyInterpretation.isExistQuantified(freeVar)) : "unbound variable in condition is not matched by any term variable";
                }

                IDependencyGraph.assertUsedVariables(usedVariables, entry.getValue().getBoundVariables());
            }
        }

        // check sorted initial nodes
        if (Globals.useAssertions) {
            for (final Map.Entry<IFunctionSymbol<?>, ImmutableSet<INode>> fsNodes : initialRewriteNodes.entrySet()) {
                assert nodes.keySet().containsAll(fsNodes.getValue()) : "all initial nodes must be contained in the graph";
                if (fsNodes.getKey() != null) {
                    for (final INode node : fsNodes.getValue()) {
                        assert ((IFunctionApplication<?>) nodes.get(node)).getRootSymbol().equals(fsNodes.getKey()) : "bad sorting of initial nodes";
                    }
                } else {
                    for (final INode node : fsNodes.getValue()) {
                        assert nodes.get(node).isVariable() : "bad sorting of initial nodes";;
                    }
                }
            }
        }

        // qTerms initial nodes
        if (Globals.useAssertions) {
            for (final ITerm<?> qTerm: q.getUserDefinedTerms()) {
                final Set<IVariable<?>> termVars = qTerm.getVariables();
                IDependencyGraph.assertUsedVariables(usedVariables, termVars);
            }
        }

        if (Globals.useAssertions) {
            assert(freshVarNameGenerator.isUsed(usedVariables)) : "not all used variables are contained in fresh var generator";
        }
        return maxNodeId;
    }

    private static void assertUsedVariables(final Set<IVariable<?>> usedVariables,
        final Collection<? extends IVariable<?>> addVariables) {
        for (final IVariable<?> var : addVariables) {
            assert usedVariables.add(var) : "dupplicate variable " + var;
        }
    }

    private static ImmutableMap<IFunctionSymbol<?>, ImmutableSet<INode>> sortInitialNodes(final ImmutableMap<INode, ITerm<?>> nodes,
        final ImmutableSet<INode> initialNodes) {
        final CollectionMap<IFunctionSymbol<?>, INode> sortedInitialNodes =
            new CollectionMap<IFunctionSymbol<?>, INode>();

        for (final INode initialNode : initialNodes) {
            final ITerm<?> nodeTerm = nodes.get(initialNode);
            if (nodeTerm.isVariable()) {
                sortedInitialNodes.add(null, initialNode);
            } else {
                sortedInitialNodes.add(((IFunctionApplication<?>) nodeTerm).getRootSymbol(), initialNode);
            }
        }

        return CollectionUtil.immutableCollectionMap(sortedInitialNodes);
    }

    private static PositionalMatchUnification<INode> createInitialRewriteNodesMatching(final Map<INode, ? extends ITerm<?>> nodes,
        final ImmutableMap<IFunctionSymbol<?>, ImmutableSet<INode>> initialNodes) {
        final Map<ITerm<?>, INode> matching = new LinkedHashMap<ITerm<?>, INode>();

        for (final ImmutableSet<INode> initialNodesSet : initialNodes.values()) {
            for (final INode initialNode : initialNodesSet) {
                matching.put(nodes.get(initialNode), initialNode);
            }
        }

        return new PositionalMatchUnification<INode>(matching);
    }

    protected static void checkEdges(final Set<INode> nodes,
        final Set<IEdge> edges) {
        final Iterator<IEdge> i = edges.iterator();
        while (i.hasNext()) {
            final IEdge edge = i.next();
            final INode from = edge.from;
            final INode to = edge.to;
            assert (nodes.contains(from) && nodes.contains(to)) : "invalid edge : "
                + edge;
        }
    }

    private final Integer maxNodeId;
    private final SideConstraintStore sideConstraints;

    private final IQTermSet q;
    private final ImmutableMap<INode, ? extends ITerm<?>> nodes;
    private final ImmutableMap<INode, Integer> nodeUnrollCounter;
    private final ImmutableMap<IFunctionSymbol<?>, ImmutableSet<INode>> initialRewriteNodes;

    private final ImmutableMap<INode, Itpf> nodeConditions;
    private final ImmutableMap<INode, VarRenaming> loopRenamings;
    private final ImmutableSet<INode> immuNodes;
    private final ImmutableSet<IEdge> immuEdges;
    private final ImmutableMap<IEdge, Itpf> edges;

    private final MarksHandler<Singleton<IDependencyGraph>, IDependencyGraph, IDependencyGraph> marks;

    private volatile TermAnalysis<ITerm<?>> termAnalysis;

    private volatile ImmutableMap<INode, ImmutableMap<INode, ImmutableSet<IEdge>>> post;
    private volatile ImmutableMap<INode, ImmutableMap<INode, ImmutableSet<IEdge>>> pre;

    private volatile ImmutableSet<IVariable<?>> variables;
    private volatile ImmutableSet<IFunctionSymbol<?>> definedSymbols;

    private final ItpfFactory itpfFactory;
    private final PolyInterpretation<?> polyInterpretation;
    private final PolyFactory polyFactory;

    private final FreshVarGenerator freshVarNameGenerator;

    private final PositionalMatchUnification<INode> initialRewriteNodesMatching;



    private IDependencyGraph(
            final IDPPredefinedMap predefinedMap,
            final ItpfFactory itpfFactory,
            final PolyInterpretation<?> polyInterpretation,
            final IQTermSet q,
            final ImmutableMap<INode, ? extends ITerm<?>> nodes,
            final ImmutableMap<INode, Itpf> nodeConditions,
            final ImmutableMap<IFunctionSymbol<?>, ImmutableSet<INode>> initialNodes,
            final ImmutableMap<INode, Integer> nodeUnrollCounter,
            final ImmutableMap<INode, VarRenaming> loopRenamings,
            final ImmutableMap<IEdge, Itpf> edges,
            final ImmutableMap<INode, ImmutableMap<INode, ImmutableSet<IEdge>>> pre,
            final ImmutableMap<INode, ImmutableMap<INode, ImmutableSet<IEdge>>> post,
            final FreshVarGenerator freshVarNameGenerator,
            final Integer maxNodeId) {
        this(itpfFactory, polyInterpretation, q, nodes, nodeConditions, initialNodes,
            IDependencyGraph.createInitialRewriteNodesMatching(nodes, initialNodes), nodeUnrollCounter,
            loopRenamings, edges, pre, post, freshVarNameGenerator, maxNodeId);
    }

    private IDependencyGraph(
            final ItpfFactory itpfFactory,
            final PolyInterpretation<?> polyInterpretation,
            final IQTermSet q,
            final ImmutableMap<INode, ? extends ITerm<?>> nodes,
            final ImmutableMap<INode, Itpf> nodeConditions,
            final ImmutableMap<IFunctionSymbol<?>, ImmutableSet<INode>> initialRewriteNodes,
            final PositionalMatchUnification<INode> initialRewriteNodesMatching,
            final ImmutableMap<INode, Integer> nodeUnrollCounter,
            final ImmutableMap<INode, VarRenaming> loopRenamings,
            final ImmutableMap<IEdge, Itpf> edges,
            final ImmutableMap<INode, ImmutableMap<INode, ImmutableSet<IEdge>>> pre,
            final ImmutableMap<INode, ImmutableMap<INode, ImmutableSet<IEdge>>> post,
            final FreshVarGenerator freshVarNameGenerator,
            final Integer maxNodeId) {

        if (Globals.useAssertions) {
            assert polyInterpretation == null || polyInterpretation.getConstraintFactory() == itpfFactory;
            this.assertPolyInterpretation(polyInterpretation, edges.values());
            this.assertPolyInterpretation(polyInterpretation,
                nodeConditions.values());
        }
        this.freshVarNameGenerator = freshVarNameGenerator;
        this.sideConstraints = new SideConstraintStore(this);
        this.itpfFactory = itpfFactory;
        this.polyFactory = itpfFactory.getPolyFactory();
        this.polyInterpretation = polyInterpretation;
        this.marks = new MarksHandler<Singleton<IDependencyGraph>, IDependencyGraph, IDependencyGraph> (this);
        this.nodes = nodes;
        this.nodeUnrollCounter = nodeUnrollCounter;
        this.initialRewriteNodes = initialRewriteNodes;
        this.initialRewriteNodesMatching = initialRewriteNodesMatching;
        this.nodeConditions = nodeConditions;
        this.q = q;
        this.loopRenamings = loopRenamings;
        this.immuNodes = ImmutableCreator.create(nodes.keySet());
        this.edges = edges;
        this.immuEdges = ImmutableCreator.create(edges.keySet());
        this.pre = pre;
        this.post = post;
        this.maxNodeId = maxNodeId;
    }

    private void assertPolyInterpretation(final PolyInterpretation<?> polyInterpretation,
        final Collection<Itpf> formulas) {
        for (final Itpf formula : formulas) {
            for (final ItpfConjClause clause : formula.getClauses()) {
                for (final ItpfAtom atom : clause.getLiterals().keySet()) {
                    if (atom.isPoly()) {
                        assert ((ItpfPolyAtom<?>) atom).getInterpretation().equals(
                            polyInterpretation) : "inconsistent poly interpretation";
                    } else if (atom.isImplication()) {
                        final ItpfImplication implication = (ItpfImplication) atom;
                        this.assertPolyInterpretation(polyInterpretation, Collections.singleton(implication.getPrecondition()));
                        this.assertPolyInterpretation(polyInterpretation, Collections.singleton(implication.getConclusion()));
                    }
                }
            }
        }
    }

    // #############################################################################
    // Graph Building
    // #############################################################################
    protected void buildPrePost() {
        if (this.pre == null) {
            synchronized (this) {
                if (this.pre == null) {
                    final Map<INode, CollectionMap<INode, IEdge>> preMap =
                        new LinkedHashMap<INode, CollectionMap<INode, IEdge>>();
                    final Map<INode, CollectionMap<INode, IEdge>> postMap =
                        new LinkedHashMap<INode, CollectionMap<INode, IEdge>>();
                    for (final INode n : this.nodes.keySet()) {
                        preMap.put(n, new CollectionMap<INode, IEdge>());
                        postMap.put(n, new CollectionMap<INode, IEdge>());
                    }
                    for (final IEdge edge : this.edges.keySet()) {
                        preMap.get(edge.to).add(edge.from, edge);
                        postMap.get(edge.from).add(edge.to, edge);
                    }
                    final Map<INode, ImmutableMap<INode, ImmutableSet<IEdge>>> preImmu =
                        new LinkedHashMap<INode, ImmutableMap<INode, ImmutableSet<IEdge>>>();
                    final Map<INode, ImmutableMap<INode, ImmutableSet<IEdge>>> postImmu =
                        new LinkedHashMap<INode, ImmutableMap<INode, ImmutableSet<IEdge>>>();
                    for (final Map.Entry<INode, CollectionMap<INode, IEdge>> entry : preMap.entrySet()) {
                        final LinkedHashMap<INode, ImmutableSet<IEdge>> map =
                            new LinkedHashMap<INode, ImmutableSet<IEdge>>();
                        for (final Map.Entry<INode, Collection<IEdge>> nodeEntry : entry.getValue().entrySet()) {
                            map.put(
                                nodeEntry.getKey(),
                                ImmutableCreator.create((LinkedHashSet<IEdge>) nodeEntry.getValue()));
                        }
                        preImmu.put(entry.getKey(),
                            ImmutableCreator.create(map));
                    }
                    for (final Map.Entry<INode, CollectionMap<INode, IEdge>> entry : postMap.entrySet()) {
                        final LinkedHashMap<INode, ImmutableSet<IEdge>> map =
                            new LinkedHashMap<INode, ImmutableSet<IEdge>>();
                        for (final Map.Entry<INode, Collection<IEdge>> nodeEntry : entry.getValue().entrySet()) {
                            map.put(
                                nodeEntry.getKey(),
                                ImmutableCreator.create((LinkedHashSet<IEdge>) nodeEntry.getValue()));
                        }
                        postImmu.put(entry.getKey(),
                            ImmutableCreator.create(map));
                    }
                    this.pre = ImmutableCreator.create(preImmu);
                    this.post = ImmutableCreator.create(postImmu);
                }
            }
        }
    }

    /**
     * Changes some conditions for nodes and edges. May also add edges.
     * @param newNodeConditions New conditions for a subset of the graphs nodes.
     * @param newEdgeConditions New conditions for a subset of the graphs edges.
     * @return The chnaged graph.
     */
    public IDependencyGraph change(Map<INode, Itpf> newNodeConditions,
        Map<IEdge, Itpf> newEdgeConditions,
        ImmutableMap<IFunctionSymbol<?>, ImmutableSet<INode>> newInitialRewriteNodes,
        PolyInterpretation<?> newPolyInterpretation,
        Set<INode> unrolledNodes,
        final Mark<? extends Result> processorMark) {

        if (newNodeConditions == null) {
            newNodeConditions = Collections.<INode, Itpf> emptyMap();
        }

        if (newEdgeConditions == null) {
            newEdgeConditions = Collections.emptyMap();
        }

        if (newPolyInterpretation == null) {
            newPolyInterpretation = this.polyInterpretation;
        }

        if (newInitialRewriteNodes == null) {
            newInitialRewriteNodes = this.initialRewriteNodes;
        }

        if (unrolledNodes == null) {
            unrolledNodes = Collections.emptySet();
        }

        if (Globals.useAssertions) {
            assert this.nodes.keySet().containsAll(newNodeConditions.keySet()) : "do not introduce new nodes here!";
            assert this.nodes.keySet().containsAll(unrolledNodes) : "only nodes in this graph can be unrolled";
        }

        if (newNodeConditions.isEmpty() && newEdgeConditions.isEmpty()
            && newPolyInterpretation == this.polyInterpretation
            && newInitialRewriteNodes.isEmpty()) {
            this.marks.setMark(processorMark, new Singleton<IDependencyGraph>(this), null);
            return this;
        }

        final Map<INode, ? extends ITerm<?>> changedNodes;
        final CollectionMap<IFunctionSymbol<?>, INode> newMutableInitialNodes = new CollectionMap<IFunctionSymbol<?>, INode>();
        for (final Map.Entry<IFunctionSymbol<?>, ImmutableSet<INode>> initialNodesEntry : newInitialRewriteNodes.entrySet()) {
            newMutableInitialNodes.add(initialNodesEntry.getKey(), initialNodesEntry.getValue());
        }

        final Map<INode, Itpf> changedNodeConditions;
        final Map<INode, VarRenaming> changedLoopRenamings;
        boolean removedOrAddedNode;
        if (newNodeConditions.isEmpty()) {
            removedOrAddedNode = false;
            changedNodes = this.nodes;
            changedNodeConditions = this.nodeConditions;
            changedLoopRenamings = this.loopRenamings;
        } else {
            removedOrAddedNode = false;
            changedNodes = new LinkedHashMap<INode, ITerm<?>>(this.nodes);
            changedNodeConditions =
                new LinkedHashMap<INode, Itpf>(this.nodeConditions);
            changedLoopRenamings =
                new LinkedHashMap<INode, VarRenaming>(this.loopRenamings);
            for (final Map.Entry<INode, Itpf> entry : newNodeConditions.entrySet()) {
                final INode node = entry.getKey();
                final Itpf newCondition = entry.getValue();
                if (!newCondition.isFalse()) {
                    changedNodeConditions.put(node, newCondition);
                } else if (changedNodes.remove(node) != null) {
                    changedNodeConditions.remove(node);
                    changedLoopRenamings.remove(node);

                    final ITerm<?> nodeTerm = this.nodes.get(node);
                    if (nodeTerm.isVariable()) {
                        newMutableInitialNodes.removeFromCollection(null, node);
                    } else {
                        newMutableInitialNodes.removeFromCollection(((IFunctionApplication<?>) nodeTerm).getRootSymbol(), node);
                    }

                    removedOrAddedNode = true;
                }
            }
        }

        final ImmutableMap<IFunctionSymbol<?>, ImmutableSet<INode>> newInitialNodes =
            CollectionUtil.immutableCollectionMap(newMutableInitialNodes);

        final Map<IEdge, Itpf> changedEdges =
            new LinkedHashMap<IEdge, Itpf>();

        boolean removedOrAddedEdge =
            this.edges.keySet().containsAll(newEdgeConditions.keySet());

        for (final Map.Entry<IEdge, Itpf> entry : this.edges.entrySet()) {
            final IEdge edge = entry.getKey();
            if (changedNodes.containsKey(edge.from)
                && changedNodes.containsKey(edge.to)) {
                changedEdges.put(entry.getKey(), entry.getValue());
            } else {
                removedOrAddedEdge = true;
            }
        }

        for (final Map.Entry<IEdge, Itpf> entry : newEdgeConditions.entrySet()) {
            final IEdge edge = entry.getKey();
            if (edge.type != EdgeType.NO_EDGE
                    && changedNodes.containsKey(edge.from)
                    && changedNodes.containsKey(edge.to)) {
                final Itpf newCondition = entry.getValue();
                if (!newCondition.isFalse()) {
                    changedEdges.put(edge, newCondition);
                } else if (changedEdges.remove(edge) != null) {
                    removedOrAddedEdge = true;
                }
            } else if (changedEdges.remove(edge) != null) {
                removedOrAddedEdge = true;
            }
        }

        final Map<INode, Integer> newNodeUnrollCounter = this.increaseNodeUnrollCounter(unrolledNodes);
        newNodeUnrollCounter.keySet().retainAll(changedNodes.keySet());

        final IDependencyGraph newGraph;
        if (removedOrAddedNode) {
            synchronized (this) {
                newGraph =
                    new IDependencyGraph(this.getItpfFactory(),
                        newPolyInterpretation, this.q,
                        ImmutableCreator.create(changedNodes),
                        ImmutableCreator.create(changedNodeConditions),
                        newInitialNodes,
                        IDependencyGraph.createInitialRewriteNodesMatching(changedNodes, newInitialNodes),
                        ImmutableCreator.create(newNodeUnrollCounter),
                        ImmutableCreator.create(changedLoopRenamings),
                        ImmutableCreator.create(changedEdges),
                        removedOrAddedEdge ? null : this.pre, removedOrAddedEdge
                            ? null : this.post,
                                this.freshVarNameGenerator,
                                this.maxNodeId);
            }
        } else {
            final boolean removedTerm =
                !changedNodes.values().containsAll(this.nodes.values());

            final PositionalMatchUnification<INode> newInitialRewriteNodesMatching;
            if (removedTerm || !this.initialRewriteNodes.equals(newInitialNodes)) {
                newInitialRewriteNodesMatching = IDependencyGraph.createInitialRewriteNodesMatching(changedNodes, newInitialNodes);
            } else {
                newInitialRewriteNodesMatching = this.initialRewriteNodesMatching;
            }

            IDependencyGraph.assertGraphProperties(
                this.q,
                newPolyInterpretation,
                changedNodes,
                newNodeUnrollCounter,
                changedLoopRenamings,
                changedNodeConditions,
                newInitialNodes,
                changedEdges,
                this.freshVarNameGenerator);

            newGraph =
                new IDependencyGraph(this.getItpfFactory(),
                    newPolyInterpretation, this.q,
                    ImmutableCreator.create(changedNodes),
                    ImmutableCreator.create(changedNodeConditions),
                    newInitialNodes,
                    newInitialRewriteNodesMatching,
                    ImmutableCreator.create(newNodeUnrollCounter),
                    ImmutableCreator.create(changedLoopRenamings),
                    ImmutableCreator.create(changedEdges), null, null,
                    this.freshVarNameGenerator,
                    this.maxNodeId);
        }

        this.marks.copyCompatibleMarks(newGraph, processorMark);
        this.marks.setMark(processorMark, new Singleton<IDependencyGraph>(newGraph), null);
        newGraph.sideConstraints.copySignatureFrom(this.sideConstraints);

        return newGraph;
    }

    private Map<INode, Integer> increaseNodeUnrollCounter(final Set<INode> unrolledNodes) {
        final Map<INode, Integer> result = new LinkedHashMap<INode, Integer>(this.nodeUnrollCounter);

        for (final INode node : unrolledNodes) {
            result.put(node, result.get(node) + 1);
        }

        return result;
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
        final VerbosityLevel verbosityLevel) {

        this.buildPrePost();
        if (!this.nodes.isEmpty()) {
            // s.append(o.set(this.P, Export_Util.RULES));
            for (final Map.Entry<INode, ? extends ITerm<?>> n : this.nodes.entrySet()) {
                final StringBuilder indent = new StringBuilder();
                n.getKey().export(indent, o, verbosityLevel);
                if (this.isInitialRewriteNode(n.getKey())) {
                    indent.append(" * ");
                }
                indent.append(": ");
                indent.append(n.getValue().export(o));
                sb.append(o.indent(indent.toString()));
                sb.append(o.linebreak());
            }
            sb.append(o.linebreak());
            final List<Map.Entry<IEdge, Itpf>> sortedEdges =
                new ArrayList<Map.Entry<IEdge, Itpf>>(this.edges.entrySet());
            Collections.sort(sortedEdges, EdgeComparator.EDGE_ENTRY_COMPARATOR);

            for (final Map.Entry<IEdge, Itpf> edgeEntry : sortedEdges) {
                for (final ItpfConjClause clause : edgeEntry.getValue().getClauses()) {
                    final Itpf condition = this.itpfFactory.create(edgeEntry.getValue().getQuantification(), clause);
                    final ISubstitution condtitionSubstitution = this.extractSubstitution(clause);

                    final IEdge edge = edgeEntry.getKey();
                    final StringBuilder indent = new StringBuilder();
                    indent.append(edge.type.export(o));
                    indent.append(": ");

                    edge.from.export(indent, o, VerbosityLevel.LOW);
                    if (!edge.fromPos.isEmptyPosition()) {
                        indent.append("@");
                        indent.append(edge.fromPos.export(o));
                    }

                    final ITerm<?> fromTerm = this.getTerm(edge.from);
                    final StringBuilder fromTermExport = new StringBuilder();
                    fromTerm.applySubstitution(condtitionSubstitution).export(fromTermExport, o, VerbosityLevel.LOW);
                    if (fromTermExport.length() < IDependencyGraph.MAX_NODE_TERM_EXPORT_LENGTH) {
                        indent.append(":");
                        indent.append(fromTermExport);
                    } else {
                        final ISubstitution fromRestrictedCondSubstitution = condtitionSubstitution.
                            restrictTo(fromTerm.getSubterm(edge.fromPos)
                                .getVariables());

                        if (!fromRestrictedCondSubstitution.isEmpty()) {
                            indent.append(fromRestrictedCondSubstitution.export(o));
                        }
                    }

                    indent.append(" -> ");
                    edge.to.export(indent, o, VerbosityLevel.LOW);

                    ISubstitution toSubstitution;
                    if (edge.from.equals(edge.to)) {
                        toSubstitution = ISubstitution.create(this.loopRenamings.get(edge.from));
                    } else {
                        toSubstitution = ISubstitution.emptySubstitution();
                    }

                    final ITerm<?> toTerm = this.getTerm(edge.to);
                    final StringBuilder toTermExport = new StringBuilder();
                    toTerm.
                        applySubstitution(toSubstitution).
                        applySubstitution(condtitionSubstitution).
                        export(toTermExport, o, VerbosityLevel.LOW);

                    if (toTermExport.length() < IDependencyGraph.MAX_NODE_TERM_EXPORT_LENGTH) {
                        indent.append(":");
                        indent.append(toTermExport);
                    } else {
                        final ISubstitution toRestrictedCondSubstitution = toSubstitution.
                            termCompose(condtitionSubstitution).
                            restrictTo(toTerm.getVariables());

                        if (!toRestrictedCondSubstitution.isEmpty()) {
                            indent.append(toRestrictedCondSubstitution.export(o));
                        }
                    }

                    if (!condition.isTrue()) {
                        indent.append(" :|: ");
                        indent.append(o.linebreak());
                        condition.export(indent, o, verbosityLevel);
                    }

                    sb.append(o.indent(indent.toString()));
                    sb.append(o.linebreak());
                }
            }
            sb.append(o.cond_linebreak());
        }

        sb.append("Q contains the following terms:");
        sb.append(o.cond_linebreak());
        this.q.export(sb, o, verbosityLevel);

        sb.append(o.cond_linebreak());
        if (this.polyInterpretation != null) {
            sb.append("The following polynomial interpretation is used:");
            sb.append(o.cond_linebreak());
            this.polyInterpretation.export(sb, o, verbosityLevel);
        }

    }

    private ISubstitution extractSubstitution(final ItpfConjClause clause) {
        final LinkedHashMap<IVariable<?>, ITerm<?>> resMap = new LinkedHashMap<IVariable<?>, ITerm<?>>();

        for (final Map.Entry<? extends ItpfAtom, Boolean> literal : clause.getLiterals().entrySet()) {
            if (literal.getValue()) {
                if (literal.getKey().isItp()) {
                    final ItpfItp itp = (ItpfItp) literal.getKey();
                    if (itp.getRelation() == ItpRelation.EQ) {
                        if (itp.getL().isVariable()) {
                            resMap.put((IVariable<?>) itp.getL(), itp.getR());
                        } else if (itp.getR().isVariable()) {
                            resMap.put((IVariable<?>) itp.getR(), itp.getL());
                        }
                    }
                }
            }
        }

        return ISubstitution.create(ImmutableCreator.create(resMap));
    }

    /**
     * Returns a formatting String for the DOT representation of a node label in
     * this graph dependent on the method called for the representation, the
     * node and a parameter object.
     * @param method An integer constant describing the calling method for DOT
     * representation. Can be DOT, SAVE, EDGES, INTERACTIVE, DOTDOT1 or DOTDOT2.
     * @param node The node labeled with this format.
     * @return A formatting String for the DOT representation of a node label in
     * this graph.
     */
    protected String getDOTFormatForNodeLabels(final int method, final INode node) {
        switch (method) {
        case DOT:
        case DOTDOT2:
            return "fontsize=16";
        case SAVE:
        case EDGES:
        case DOTDOT1:
            return "fontsize=16";
        case INTERACTIVE:
            return "fontsize=10";
        }
        return "";
    }

    /**
     * Returns the label text of a node in the DOT representation of this graph
     * dependent on the calling method for the DOT representation and the node.
     * @param method An integer constant describing the calling method for DOT
     * representation. Can be DOT, SAVE, EDGES or INTERACTIVE.
     * @param node The node to be labeled with the text.
     * @return The specified node's label text in the DOT representation.
     */
    protected String getDOTNodeLabelText(final int method, final INode node) {
        switch (method) {
        case DOT:
        case SAVE:
            return node.export(new Dotty_Util());
        case EDGES:
        case INTERACTIVE:
            return node.export(new Dotty_Util());
        }
        return "";
    }

    public ImmutableSet<IEdge> getEdges() {
        return this.immuEdges;
    }

    public ImmutableMap<IEdge, Itpf> getEdgeConditions() {
        return this.edges;
    }

    public int getInDegree(final INode node) {
        this.buildPrePost();
        int degree = 0;
        for (final Collection<IEdge> edgeSet : this.pre.get(node).values()) {
            degree += edgeSet.size();
        }
        return degree;
    }

    public int getInDegree(final INode node, final Collection<EdgeType> types) {
        this.buildPrePost();
        int degree = 0;
        for (final Collection<IEdge> edgeSet : this.pre.get(node).values()) {
            for (IEdge edge : edgeSet) {
                if (types.contains(edge.type)) {
                    degree += 1;
                }
            }
        }
        return degree;
    }

    public ImmutableSet<INode> getNodes() {
        return this.immuNodes;
    }

    public ImmutableMap<INode, ? extends ITerm<?>> getNodeMap() {
        return this.nodes;
    }

    public ImmutableMap<IFunctionSymbol<?>, ImmutableSet<INode>> getInitialRewriteNodes() {
        return this.initialRewriteNodes;
    }

    public boolean isInitialRewriteNode(final INode node) {
        final ITerm<?> nodeTerm = this.nodes.get(node);
        final ImmutableSet<INode> initials;
        if (!nodeTerm.isVariable()) {
            initials = this.initialRewriteNodes.get(((IFunctionApplication<?>) nodeTerm).getRootSymbol());
        } else {
            initials = this.initialRewriteNodes.get(null);
        }
        return initials != null && initials.contains(node);
    }

    public boolean containsInitialRewriteNode(final Collection<IEdge> path) {
        for (final IEdge edge : path) {
            if (this.isInitialRewriteNode(edge.from)) {
                return true;
            }
        }

        return false;
    }

    public ImmutableMap<INode, Itpf> getNodeConditions() {
        return this.nodeConditions;
    }

    public VarRenaming getLoopRenaming(final INode node) {
        return this.loopRenamings.get(node);
    }

    public ImmutableMap<INode, Integer> getNodeUnrollCounter() {
        return this.nodeUnrollCounter;
    }

    public ImmutableMap<INode, VarRenaming> getLoopRenamings() {
        return this.loopRenamings;
    }

    public int getOutDegree(final INode node) {
        this.buildPrePost();
        int degree = 0;
        for (final Collection<IEdge> edgeSet : this.post.get(node).values()) {
            degree += edgeSet.size();
        }
        return degree;
    }

    public int getOutDegree(final INode node, final Collection<EdgeType> types) {
        this.buildPrePost();
        int degree = 0;
        for (final Collection<IEdge> edgeSet : this.post.get(node).values()) {
            for (IEdge edge : edgeSet) {
                if (types.contains(edge.type)) {
                    degree += 1;
                }
            }
        }
        return degree;
    }

    public int getPosDependentOutDegree(final INode node, final Collection<EdgeType> types) {
        this.buildPrePost();
        Set<IPosition> positions = new LinkedHashSet<>();
        int degree = 0;
        for (final Collection<IEdge> edgeSet : this.post.get(node).values()) {
            for (IEdge edge : edgeSet) {
                if (types.contains(edge.type) && !positions.contains(edge.fromPos)) {
                    positions.add(edge.fromPos);
                    degree += 1;
                }
            }
        }
        return degree;
    }

    public ImmutableMap<INode, ImmutableSet<IEdge>> getPredecessors(final INode node) {
        this.buildPrePost();
        return this.pre.get(node);
    }

    public ImmutableMap<INode, ImmutableMap<INode, ImmutableSet<IEdge>>> getPredecessors() {
        this.buildPrePost();
        return this.pre;
    }

    public ImmutableMap<INode, ImmutableMap<INode, ImmutableSet<IEdge>>> getSuccessors() {
        this.buildPrePost();
        return this.post;
    }

    public FreshVarGenerator getFreshVarGenerator() {
        return this.freshVarNameGenerator;
    }

    public ITerm<?> getTerm(final INode node) {
        return this.nodes.get(node);
    }

    public Itpf getCondition(final IEdge edge) {
        return this.edges.get(edge);
    }

    public Itpf getCondition(final INode node) {
        return this.nodeConditions.get(node);
    }

    public Map<INode, Pair<VarRenaming, ISubstitution>> getRootMatchingNodes(final ITerm<?> term, final boolean requireOutgoingEdge) {
        return this.getRootUnifyingMatchingNodes(term, requireOutgoingEdge, true);
    }

    public Map<INode, Pair<VarRenaming, ISubstitution>> getRootUnifyingNodes(final ITerm<?> term, final boolean requireOutgoingEdge) {
        return this.getRootUnifyingMatchingNodes(term, requireOutgoingEdge, false);
    }

    private Map<INode, Pair<VarRenaming, ISubstitution>> getRootUnifyingMatchingNodes(final ITerm<?> term, final boolean requireOutgoingEdge, final boolean requireMatching) {
        final Map<INode, Pair<VarRenaming, ISubstitution>> matches = new LinkedHashMap<INode, Pair<VarRenaming, ISubstitution>>();
        for (final Map.Entry<INode, ? extends ITerm<?>> nodeAndTerm : this.nodes.entrySet()) {
            final INode node = nodeAndTerm.getKey();
            if (requireOutgoingEdge && this.getSuccessors(node).isEmpty()) {
                continue;
            }

            final VarRenaming nodeFreshVars = this.getFreshVarsRenaming(nodeAndTerm.getValue());
            final ITerm<?> renamedNodeTerm = nodeAndTerm.getValue().applySubstitution(nodeFreshVars);
            final Set<IVariable<?>> nodeVariables = renamedNodeTerm.getVariables();

            if (renamedNodeTerm.isVariable()) {
                final IVariable<?> renamedNodeTermVar = (IVariable<?>) renamedNodeTerm;
                if (renamedNodeTerm.getDomain().isSpecialization(term.getDomain())) {
                    matches.put(node, new Pair<VarRenaming, ISubstitution>(nodeFreshVars, ISubstitution.create(renamedNodeTermVar, term)));
                }
            } else {
                final IFunctionApplication<?> nodeFa = (IFunctionApplication<?>) renamedNodeTerm;

                if (requireMatching) {
                    final ISubstitution matcher = nodeFa.getMatcher(term);
                    if (matcher != null) {
                        matches.put(node, new Pair<VarRenaming, ISubstitution>(nodeFreshVars, matcher));
                    }
                } else {
                    ISubstitution mgu = nodeFa.getMGU(term);
                    if (mgu != null) {
                        mgu = this.cleanMgu(mgu, nodeVariables);
                        matches.put(node, new Pair<VarRenaming, ISubstitution>(nodeFreshVars, mgu));
                    }
                }
            }
        }

        return matches;
    }


    public Map<INode, Pair<VarRenaming, Collection<Pair<IPosition, ISubstitution>>>> getMatchingNodes(final ITerm<?> term, final Map<IFunctionSymbol<?>, Collection<Pair<IPosition, ITerm<?>>>> positionsWithSubTerms, final boolean requireOutgoingEdge) {
        return this.getUnifyingMatchingNodes(term, positionsWithSubTerms, requireOutgoingEdge, true);
    }

    public Map<INode, Pair<VarRenaming, Collection<Pair<IPosition, ISubstitution>>>> getUnifyingNodes(final ITerm<?> term, final Map<IFunctionSymbol<?>, Collection<Pair<IPosition, ITerm<?>>>> positionsWithSubTerms, final boolean requireOutgoingEdge) {
        return this.getUnifyingMatchingNodes(term, positionsWithSubTerms, requireOutgoingEdge, false);
    }

    private Map<INode, Pair<VarRenaming, Collection<Pair<IPosition, ISubstitution>>>> getUnifyingMatchingNodes(final ITerm<?> term, final Map<IFunctionSymbol<?>, Collection<Pair<IPosition, ITerm<?>>>> positionsWithSubTerms, final boolean requireOutgoingEdge, final boolean requireMatching) {
        final Map<INode, Pair<VarRenaming, Collection<Pair<IPosition, ISubstitution>>>> matches = new LinkedHashMap<INode, Pair<VarRenaming, Collection<Pair<IPosition, ISubstitution>>>>();
        for (final Map.Entry<IFunctionSymbol<?>, ImmutableSet<INode>> initialNodes : this.initialRewriteNodes.entrySet()) {
            for (final INode node : initialNodes.getValue()) {
                if (requireOutgoingEdge && this.getSuccessors(node).isEmpty()) {
                    continue;
                }
                final ITerm<?> nodeTerm = this.getTerm(node);
                final VarRenaming nodeFreshVars = this.getFreshVarsRenaming(nodeTerm);
                final ITerm<?> renamedNodeTerm = nodeTerm.applySubstitution(nodeFreshVars);
                final ArrayList<Pair<IPosition, ISubstitution>> nodeMatches = new ArrayList<Pair<IPosition, ISubstitution>>();
                final Set<IVariable<?>> nodeVariables = renamedNodeTerm.getVariables();

                if (renamedNodeTerm.isVariable()) {
                    final IVariable<?> renamedNodeTermVar = (IVariable<?>) renamedNodeTerm;
                    for (final Collection<Pair<IPosition, ITerm<?>>> posTerms : positionsWithSubTerms.values()) {
                        for (final Pair<IPosition, ITerm<?>> posTerm : posTerms) {
                            if (renamedNodeTerm.getDomain().isSpecialization(posTerm.y.getDomain())) {
                                nodeMatches.add(new Pair<IPosition, ISubstitution> (posTerm.x, ISubstitution.create(renamedNodeTermVar, posTerm.y)));
                            }
                        }
                    }
                } else {
                    final IFunctionApplication<?> nodeFa = (IFunctionApplication<?>) renamedNodeTerm;
                    final Collection<Pair<IPosition, ITerm<?>>> possiblePositions = positionsWithSubTerms.get(nodeFa.getRootSymbol());

                    if (possiblePositions != null) {
                        for (final Pair<IPosition, ITerm<?>> posTerm : possiblePositions ) {
                            if (requireMatching) {
                                final ISubstitution matcher = nodeFa.getMatcher(posTerm.y);
                                if (matcher != null) {
                                    nodeMatches.add(new Pair<IPosition, ISubstitution> (posTerm.x, matcher));
                                }
                            } else {
                                ISubstitution mgu = nodeFa.getMGU(posTerm.y);
                                if (mgu != null) {
                                    mgu = this.cleanMgu(mgu, nodeVariables);
                                    nodeMatches.add(new Pair<IPosition, ISubstitution> (posTerm.x, mgu));
                                }
                            }
                        }
                    }
                }

                if (!nodeMatches.isEmpty()) {
                    matches.put(node, new Pair<VarRenaming, Collection<Pair<IPosition,ISubstitution>>>(nodeFreshVars, nodeMatches));
                }
            }
        }
//
//        CollectionMap<IPosition, TermMatchUnif<INode>> fastResult;
//        if (requireMatching) {
//            fastResult = initialRewriteNodesMatching.getMatchesToTerm(term);
//        } else {
//            fastResult = initialRewriteNodesMatching.getMatchesToTerm(term);
//        }
//
//        for (final Map.Entry<INode, Pair<VarRenaming, Collection<Pair<IPosition, ISubstitution>>>> matchesEntry : matches.entrySet()) {
//            final INode node = matchesEntry.getKey();
//            final ITerm<?> nodeTerm = getTerm(node).applySubstitution(matchesEntry.getValue().x);
//            for (final Pair<IPosition, ISubstitution> match : matchesEntry.getValue().y) {
//                final ITerm<?> matchingNodeTerm = nodeTerm.applySubstitution(match.y);
//                final Collection<TermMatchUnif<INode>> fastPosMatches = fastResult.get(match.x);
//                boolean foundMatch = false;
//                for (final TermMatchUnif<INode> fastPosMatch : fastPosMatches) {
//                    if (fastPosMatch.getKey().equals(node)
//                            && matchingNodeTerm.equals(fastPosMatch.getTerm().applySubstitution(fastPosMatch.getMatcher()))) {
//                        foundMatch = true;
//                    }
//                }
//
//                assert foundMatch : "missing match";
//            }
//        }

        return matches;
    }

    private ISubstitution cleanMgu(final ISubstitution uncleanMgu, final Set<IVariable<?>> nodeVariables) {
        // if mgu contains x / y where x is contained in itp term and y in node term, we apply y / x to the mgu
        final Map<IVariable<?>, IVariable<?>> cleaningVarRenaming =
            new LinkedHashMap<IVariable<?>, IVariable<?>>();

        for (final Map.Entry<IVariable<?>, ? extends ITerm<?>> substEntry : uncleanMgu.getMap().entrySet()) {
            if (!nodeVariables.contains(substEntry.getKey())
                && substEntry.getValue().isVariable()) {
                final IVariable<?> targetVar =
                    (IVariable<?>) substEntry.getValue();
                if (nodeVariables.contains(targetVar)) {
                    cleaningVarRenaming.put(targetVar, substEntry.getKey());
                }
            }
        }

        if (!cleaningVarRenaming.isEmpty()) {
            return uncleanMgu.termCompose(ISubstitution.create(ImmutableCreator.create(cleaningVarRenaming)));
        } else {
            return uncleanMgu;
        }

    }

    public VarRenaming getFreshVarsRenaming(final ITerm<?> nodeTerm) {
        final Map<IVariable<?>, IVariable<?>> varRenaming = new LinkedHashMap<IVariable<?>, IVariable<?>>();

        for (final IVariable<?> var : nodeTerm.getVariables()) {
            varRenaming.put(var, this.freshVarNameGenerator.getFreshVariable(var, false));
        }

        return VarRenaming.create(ImmutableCreator.create(varRenaming), true, this.polyFactory);
    }

    public IQTermSet getQ() {
        return this.q;
    }

    @Override
    public MarksHandler<Singleton<IDependencyGraph>, IDependencyGraph, IDependencyGraph> getMarks() {
        return this.marks;
    }

    // #############################################################################
    // SCCs
    // #############################################################################
    public ImmutableList<IDPSubGraph> getEdgeSccs(final IDPSubGraph subGraph) {

        final ImmutableList<ImmutableSet<INode>> nodeSccs = this.getSCCs(subGraph.getEdges());
        final ArrayList<IDPSubGraph> edgeSccs = new ArrayList<IDPSubGraph>();

        for (final ImmutableSet<INode> scc : nodeSccs) {
            final LinkedHashSet<IEdge> sccEdges = new LinkedHashSet<IEdge>();
            for (final INode node : scc) {
                for (final Map.Entry<INode, ImmutableSet<IEdge>> succEntry : this.getSuccessors(node).entrySet()) {
                    if (scc.contains(succEntry.getKey())) {
                        for (final IEdge edge : succEntry.getValue()) {
                            if (subGraph.containsEdge(edge)) {
                                sccEdges.add(edge);
                            }
                        }
                    }
                }
            }
            edgeSccs.add(new IDPSubGraph(ImmutableCreator.create(sccEdges)));
        }
        return ImmutableCreator.create(edgeSccs);
    }

    public ImmutableList<ImmutableSet<INode>> getSCCs(final Collection<IEdge> consideredEdges) {
        this.buildPrePost();
        // do tarjan
        if (this.getNodes().isEmpty() || this.getEdges().isEmpty()
            || consideredEdges.isEmpty()) {
            ImmutableCreator.create(Collections.<ImmutableSet<INode>> emptyList());
        }

        final List<ImmutableSet<INode>> acc =
            new ArrayList<ImmutableSet<INode>>();

        final Set<INode> remainingStartNodes =
            new LinkedHashSet<INode>(GraphUtil.collectNodes(consideredEdges));

        final Map<INode, Integer> indices = new LinkedHashMap<INode, Integer>();
        final Map<INode, Integer> lowLinks = new LinkedHashMap<INode, Integer>();
        int index = 0;
        while (remainingStartNodes.size() > 0) {
            final Stack<INode> S = new Stack<INode>();
            final Iterator<INode> i = remainingStartNodes.iterator();
            final INode startNode = i.next();
            i.remove();
            index =
                this.tarjan(startNode, consideredEdges, index, S,
                    indices, lowLinks, acc);
            remainingStartNodes.removeAll(indices.keySet());
        }
        return ImmutableCreator.create(acc);
    }

    /**
     * @param node A node in the graph.
     * @return The successors for the given node.
     */
    public ImmutableMap<INode, ImmutableSet<IEdge>> getSuccessors(final INode node) {
        this.buildPrePost();
        return this.post.get(node);
    }

    /**
     * @param path A valid variable renamed path.
     * @param addExistQuantification add exitential quantification for inner steps of the path
     * @return Itpf formula that represents all conditions on the given path.
     */
    public Itpf itpfPath(final VariableRenamedPath path, final PathQuantificationMode pathQantification) {
        if (path.getPath().isEmpty()) {
            return this.getItpfFactory().createTrue();
        }

        final Set<Itpf> conj = new LinkedHashSet<Itpf>();
        Map<IVariable<?>, ? extends IVariable<?>> fromSubst = null;
        for (final ImmutablePair<IEdge, VarRenaming> step : path.getPath()) {
            final Map<IVariable<?>, ? extends IVariable<?>> toSubst;
            if (step.x.from.equals(step.x.to)) {
                final HashMap<IVariable<?>, IVariable<?>> loopSubst = new HashMap<IVariable<?>, IVariable<?>>();
                // loop -> concern about loop renaming
                for (final Map.Entry<IVariable<?>, ? extends IVariable<?>> ren : this.loopRenamings.get(
                    step.x.to).getMap().entrySet()) {
                    final IVariable<?> from = ren.getValue();
                    final IVariable<?> to = ren.getKey().applyVarSubstitution(step.y);
                    if (!from.equals(to)) {
                        loopSubst.put(from, to);
                    }
                }
                toSubst = loopSubst;
            } else {
                toSubst = step.y.getMap();
            }

            final Map<IVariable<?>, IVariable<?>> combined = new LinkedHashMap<IVariable<?>, IVariable<?>>(toSubst);
            if (fromSubst != null) {
                combined.putAll(fromSubst);
            }
            // add condition of edge from -> to
            conj.add(this.getCondition(step.x).applySubstitution(
                VarRenaming.create(ImmutableCreator.create(combined), true, this.polyInterpretation != null ? this.polyInterpretation.getFactory() : null)));

            fromSubst = step.y.getMap();
        }

        final Itpf pathCondition = this.getItpfFactory().createAnd(conj, this.freshVarNameGenerator);

        if (pathQantification != PathQuantificationMode.None) {
            final ImmutableList<ImmutablePair<IEdge, VarRenaming>> pathList =
                path.getPath();

            final ImmutablePair<IEdge, VarRenaming> firstEdge = pathList.get(0);
            final ImmutablePair<IEdge, VarRenaming> lastEdge = pathList.get(pathList.size() - 1);

            final Set<IVariable<?>> condVariables =
                new LinkedHashSet<IVariable<?>>(pathCondition.getFreeVariables());

            if (pathQantification != PathQuantificationMode.All) {
                condVariables.removeAll(this.getTerm(firstEdge.x.from).getVariables());
                condVariables.removeAll(this.getTerm(lastEdge.x.to).applySubstitution(lastEdge.y).getVariables());
            }

            return this.itpfFactory.quantifyExist(condVariables, pathCondition);
        } else {
            return pathCondition;
        }
    }

    /**
     * Generates all paths in the graph with length n and a given node at a
     * given position.
     * @param node The node for which all paths should be generated.
     * @param length The length of the path w.r.t. step (edge) count.
     * @param position The position of the node w.r.t. nodes in the path.
     * @param restrictToNodes Nodes that may occur in the paths, may be null.
     * @return A list of paths.
     */
    public List<? extends List<IEdge>> paths(final INode node,
        final int length,
        final int position,
        final Collection<INode> restrictToNodes) {
        if (position > length) {
            throw new IllegalArgumentException("position must be <= length");
        }
        if (length <= 0) {
            final ArrayList<List<IEdge>> res = new ArrayList<List<IEdge>>(1);
            res.add(new ArrayList<IEdge>(0));
            return res;
        }
        this.buildPrePost();
        final List<LinkedList<IEdge>> res = new ArrayList<LinkedList<IEdge>>();
        if (position > 0) {
            for (final Map.Entry<INode, ImmutableSet<IEdge>> preEdges : this.pre.get(
                node).entrySet()) {
                if (restrictToNodes == null
                    || restrictToNodes.contains(preEdges.getKey())) {
                    for (final IEdge preEdge : preEdges.getValue()) {
                        final LinkedList<IEdge> path = new LinkedList<IEdge>();
                        path.add(preEdge);
                        res.add(path);
                    }
                }
            }
            for (int i = position - 2; i >= 0; i--) {
                this.extendPathPre(res, restrictToNodes);
            }
            for (int i = length - position - 1; i >= 0; i--) {
                this.extendPathPost(res, restrictToNodes);
            }
        } else {
            for (final Map.Entry<INode, ImmutableSet<IEdge>> postEdges : this.post.get(
                node).entrySet()) {
                if (restrictToNodes == null
                    || restrictToNodes.contains(postEdges.getKey())) {
                    for (final IEdge postEdge : postEdges.getValue()) {
                        final LinkedList<IEdge> path = new LinkedList<IEdge>();
                        path.add(postEdge);
                        res.add(path);
                    }
                }
            }
            for (int i = length - 2; i >= 0; i--) {
                this.extendPathPost(res, restrictToNodes);
            }
        }
        return res;
    }

    protected void extendPathPost(final List<LinkedList<IEdge>> paths,
        final Collection<INode> restrictToNodes) {
        int size = paths.size();
        for (int i = 0; i < size; i++) {
            final LinkedList<IEdge> currentPath = paths.get(i);

            final INode currentNode = currentPath.getLast().to;
            final ArrayList<IEdge> succEdges = new ArrayList<IEdge>();
            for (final Map.Entry<INode, ImmutableSet<IEdge>> postEdges : this.post.get(
                currentNode).entrySet()) {
                if (restrictToNodes == null
                    || restrictToNodes.contains(postEdges.getKey())) {
                    succEdges.addAll(postEdges.getValue());
                }
            }
            if (succEdges.isEmpty()) {
                paths.remove(i);
                i--;
                size--;
            } else {
                final Iterator<IEdge> succIter = succEdges.iterator();
                final IEdge first = succIter.next();
                while (succIter.hasNext()) {
                    final LinkedList<IEdge> path =
                        new LinkedList<IEdge>(currentPath);
                    path.addLast(succIter.next());
                    paths.add(path);
                }
                currentPath.addLast(first);
            }
        }
    }

    protected void extendPathPre(final List<LinkedList<IEdge>> paths,
        final Collection<INode> restrictToNodes) {
        int size = paths.size();
        for (int i = 0; i < size; i++) {
            final LinkedList<IEdge> currentPath = paths.get(i);
            final INode currentNode = currentPath.getFirst().from;
            final ArrayList<IEdge> predecEdges = new ArrayList<IEdge>();
            for (final Map.Entry<INode, ImmutableSet<IEdge>> preEdges : this.pre.get(
                currentNode).entrySet()) {
                if (restrictToNodes == null
                    || restrictToNodes.contains(preEdges.getKey())) {
                    predecEdges.addAll(preEdges.getValue());
                }
            }

            if (predecEdges.isEmpty()) {
                paths.remove(i);
                i--;
                size--;
            } else {
                final Iterator<IEdge> predecIter = predecEdges.iterator();
                final IEdge first = predecIter.next();
                while (predecIter.hasNext()) {
                    final LinkedList<IEdge> path =
                        new LinkedList<IEdge>(currentPath);
                    path.addFirst(predecIter.next());
                    paths.add(path);
                }
                currentPath.addFirst(first);
            }
        }
    }

    private Map<INode, ImmutableMap<INode, ImmutableSet<IEdge>>> removeFromPrePostMap(final ImmutableMap<INode, ImmutableMap<INode, ImmutableSet<IEdge>>> map,
        final Collection<INode> remove) {
        final Map<INode, ImmutableMap<INode, ImmutableSet<IEdge>>> newMap =
            new LinkedHashMap<INode, ImmutableMap<INode, ImmutableSet<IEdge>>>(map);
        final Iterator<Map.Entry<INode, ImmutableMap<INode, ImmutableSet<IEdge>>>> iter =
            map.entrySet().iterator();
        while (iter.hasNext()) {
            final Map.Entry<INode, ImmutableMap<INode, ImmutableSet<IEdge>>> entry =
                iter.next();
            if (remove.contains(entry.getKey())) {
                iter.remove();
                continue;
            }
            boolean mustRemove = false;
            for (final INode node : remove) {
                if (entry.getValue().containsKey(node)) {
                    mustRemove = true;
                    break;
                }
            }
            if (mustRemove) {
                final Map<INode, ImmutableSet<IEdge>> newNodeMap =
                    new LinkedHashMap<INode, ImmutableSet<IEdge>>(
                        entry.getValue());
                newMap.keySet().removeAll(remove);
                entry.setValue(ImmutableCreator.create(newNodeMap));
            }
        }
        return newMap;
    }

    protected int tarjan(final INode v,
        final Collection<IEdge> consideredEdges,
        final int index,
        final Stack<INode> stack,
        final Map<INode, Integer> indices,
        final Map<INode, Integer> lowLinks,
        final List<ImmutableSet<INode>> sccs) {
        if (indices.containsKey(v)) {
            return index;
        }
        indices.put(v, index);
        lowLinks.put(v, index);
        final int vIndex = index;
        Integer vLow = index;
        int indx = index;
        indx++;
        stack.push(v);
        for (final Map.Entry<INode, ImmutableSet<IEdge>> succs : this.post.get(v).entrySet()) {
            final INode succ = succs.getKey();
            {
                boolean validEdge = false;
                for (final IEdge succEdge : succs.getValue()) {
                    if (consideredEdges.contains(succEdge)) {
                        validEdge = true;
                        break;
                    }
                }
                if (!validEdge) {
                    continue;
                }
            }
            final Integer toIndex = indices.get(succ);
            if (toIndex == null) {
                indx =
                    this.tarjan(succ, consideredEdges, indx, stack,
                        indices, lowLinks, sccs);
                final Integer toLow = lowLinks.get(succ);
                if (toLow < vLow) {
                    lowLinks.put(v, toLow);
                    vLow = toLow;
                }
            } else if (stack.contains(succ)) {
                if (toIndex < vLow) {
                    lowLinks.put(v, toIndex);
                    vLow = toIndex;
                }
            }
        }
        if (vLow == vIndex) {
            final Set<INode> scc = new LinkedHashSet<INode>();
            while (true) {
                final INode w = stack.pop();
                scc.add(w);
                if (v == w) {
                    break;
                }
            }
            boolean ok = scc.size() > 1;
            // check self loops
            if (!ok) {
                for (final INode succ : this.post.get(v).keySet()) {
                    if (succ == v) {
                        ok = true;
                        break;
                    }
                }
            }
            if (ok) {
                sccs.add(ImmutableCreator.create(scc));
            }
        }
        return indx;
    }

    // #############################################################################
    // DOT
    // #############################################################################

    @Override
    public String toDOT() {
        return this.toDOT(Collections.<IDPSubGraph> emptySet());
    }

    /**
     * Returns a String containing a DOT representation of this graph.
     * @return A String containing a DOT representation of this graph.
     */
    public String toDOT(final Collection<IDPSubGraph> subGraphs) {
        final StringBuffer sb =
            new StringBuffer(
                "digraph idp_graph {\nnode [outthreshold=100, inthreshold=100];\n");
        final Map<INode, StringBuffer> nodeToSubgraph =
            new HashMap<INode, StringBuffer>();
        final List<StringBuffer> subBuffers =
            new ArrayList<StringBuffer>(subGraphs.size());
        {
            int subgraphId = 0;
            for (final IDPSubGraph subgraph : subGraphs) {
                if (subgraph.isEmpty()) {
                    continue;
                }
                final StringBuffer sgrB = new StringBuffer("subgraph cluster");
                sgrB.append(subgraphId++);
                sgrB.append("{\ncolor=grey\n");
                subBuffers.add(sgrB);
                for (final INode node : GraphUtil.collectNodes(subgraph.getEdges())) {
                    nodeToSubgraph.put(node, sgrB);
                }
            }
        }
        this.buildPrePost();
        final Export_Util termExportUtil = new HTML_Util();
        for (final Map.Entry<INode, ImmutableMap<INode, ImmutableSet<IEdge>>> entry : this.post.entrySet()) {
            final StringBuffer nb = new StringBuffer();
            final INode from = entry.getKey();
            final ITerm<?> fromTerm = this.getTerm(from);
            nb.append(from.id + " [");
            nb.append("shape=none, margin=0, label=<");
            nb.append("<TABLE BORDER=\"0\" CELLBORDER=\"0\" CELLSPACING=\"0\" CELLPADDING=\"0\">");
            nb.append("<TR><TD>(");
            nb.append(entry.getKey().id);
            nb.append("): ");
            nb.append("</TD>");
            nb.append(this.dotExportTerm(fromTerm, IPosition.create(), termExportUtil));
            nb.append("</TR></TABLE>>];\n");
            StringBuffer appendTo = nodeToSubgraph.get(entry.getKey());
            if (appendTo == null) {
                appendTo = sb;
            }
            appendTo.append(nb.toString());
            if (!entry.getValue().isEmpty()) {
                for (final Map.Entry<INode, ImmutableSet<IEdge>> succs : entry.getValue().entrySet()) {
                    for (final IEdge succ : succs.getValue()) {
                        sb.append(from.id);
                        sb.append(" -> ");
                        sb.append(succs.getKey().id);
                        sb.append(" [headport=\"w\" tailport=\"");
                        sb.append(succ.fromPos.toString());
                        sb.append("\"];\n");
                    }
                }
            }
        }
        for (final StringBuffer sgrB : subBuffers) {
            sgrB.append("}\n");
            sb.append(sgrB.toString());
        }
        sb.append("}\n");
        return sb.toString();
    }

    private String dotExportTerm(final ITerm<?> t,
        final IPosition pos,
        final Export_Util eu) {
        if (t.isVariable()) {
            return "<TD>" + t.export(eu) + "</TD>";
        } else {
            final IFunctionApplication<?> fa = (IFunctionApplication<?>) t;
            final IFunctionSymbol<?> root = fa.getRootSymbol();
            final StringBuilder sb = new StringBuilder();
            if (root.getArity() == 2 && root.getSemantics() != null) {
                sb.append("<TD>");
                sb.append("(");
                sb.append("</TD>");
                sb.append(this.dotExportTerm(fa.getArgument(0), pos.append(0), eu));
                sb.append("<TD PORT=\"");
                sb.append(pos.toString());
                sb.append("\"> ");
                sb.append(root.export(eu));
                sb.append(" </TD>");
                sb.append(this.dotExportTerm(fa.getArgument(1), pos.append(1), eu));
                sb.append("<TD>");
                sb.append(")");
                sb.append("</TD>");
            } else {
                sb.append("<TD PORT=\"");
                sb.append(pos.toString());
                sb.append("\">");
                sb.append(root.export(eu));
                if (!fa.getArguments().isEmpty()) {
                    sb.append("(");
                    sb.append("</TD>");
                    for (int i = 0; i < fa.getArguments().size(); i++) {
                        sb.append(this.dotExportTerm(fa.getArgument(i),
                            pos.append(i), eu));
                        if (i < fa.getArguments().size() - 1) {
                            sb.append("<TD>, </TD>");
                        }
                    }
                    sb.append("<TD>");
                    sb.append(")");
                    sb.append("</TD>");
                } else {
                    sb.append("</TD>");
                }
            }
            return sb.toString();
        }
    }

    @Override
    public ImmutableSet<Domain> getDomains() {
        return this.createTermAnalysis().getDomains();
    }

    private TermAnalysis<ITerm<?>> createTermAnalysis() {
        if (this.termAnalysis == null) {
            synchronized (this) {
                if (this.termAnalysis == null) {
                    final LinkedHashSet<ITerm<?>> terms = new LinkedHashSet<ITerm<?>>();
                    terms.addAll(this.nodes.values());
                    for (final Itpf formula : this.nodeConditions.values()) {
                        terms.addAll(formula.getTerms(false));
                    }

                    for (final Itpf formula : this.edges.values()) {
                        terms.addAll(formula.getTerms(false));
                    }

                    this.termAnalysis = new TermAnalysis<ITerm<?>>(ImmutableCreator.create(terms), this.getPredefinedMap());
                }
            }
        }
        return this.termAnalysis;
    }

    @Override
    public ImmutableSet<IFunctionSymbol<?>> getFunctionSymbols() {
        return this.createTermAnalysis().getFunctionSymbols();
    }

    @Override
    public ImmutableSet<IFunctionSymbol<?>> getPredefinedFunctions() {
        return this.createTermAnalysis().getPredefinedFunctions();
    }

    @Override
    public IDPPredefinedMap getPredefinedMap() {
        return this.q.getPredefinedMap();
    }

    @Override
    public ImmutableSet<IFunctionSymbol<?>> getRootSymbols() {
        return this.createTermAnalysis().getRootSymbols();
    }

    public ImmutableSet<IFunctionSymbol<?>> getDefinedSymbols() {
        if (this.definedSymbols == null) {
            synchronized (this) {
                if (this.definedSymbols == null) {
                    final Set<IFunctionSymbol<?>> defined =
                        new LinkedHashSet<IFunctionSymbol<?>>();
                    for (final IEdge edge : this.edges.keySet()) {
                        final ITerm<?> fromTerm =
                            this.nodes.get(edge.from).getSubterm(edge.fromPos);
                        if (!fromTerm.isVariable()) {
                            defined.add(((IFunctionApplication<?>) fromTerm).getRootSymbol());
                        }
                    }
                    return this.definedSymbols = ImmutableCreator.create(defined);
                }
            }
        }
        return this.definedSymbols;
    }

    @Override
    public ImmutableMap<IFunctionSymbol<?>, ImmutableSet<ITerm<?>>> getTermMap() {
        return this.createTermAnalysis().getTermMap();
    }

    @Override
    public ImmutableSet<? extends ITerm<?>> getTerms() {
        return this.createTermAnalysis().getTerms();
    }

    @Override
    public ImmutableSet<IVariable<?>> getVariables() {
        if (this.variables == null) {
            synchronized (this) {
                if (this.variables == null) {
                    final Set<IVariable<?>> vars =
                        new LinkedHashSet<IVariable<?>>(
                                this.createTermAnalysis().getVariables());
                    for (final VarRenaming subst : this.loopRenamings.values()) {
                        vars.addAll(subst.getMap().values());
                    }
                    return this.variables = ImmutableCreator.create(vars);
                }
            }
        }
        return this.variables;
    }

    @Override
    public boolean hasBitwiseOps() {
        return this.createTermAnalysis().hasBitwiseOps();
    }

    @Override
    public boolean hasPredefinedDefSymbols() {
        return this.createTermAnalysis().hasPredefinedDefSymbols();
    }

    @Override
    public boolean hasRestrictedInt() {
        return this.createTermAnalysis().hasRestrictedInt();
    }

    @Override
    public boolean hasUnrestrictedInt() {
        return this.createTermAnalysis().hasUnrestrictedInt();
    }

    @Override
    public Boolean isConstructor(final IFunctionSymbol<?> fs) {
        return this.createTermAnalysis().isConstructor(fs);
    }

    public ItpfFactory getItpfFactory() {
        return this.itpfFactory;
    }

    public PolyInterpretation<?> getPolyInterpretation() {
        return this.polyInterpretation;
    }

    public SideConstraintStore getSideConstraints() {
        return this.sideConstraints;
    }

    public PolyFactory getPolyFactory() {
        return this.polyFactory;
    }

    @Override
    public Singleton<IDependencyGraph> getSelfMark() {
        return new Singleton<IDependencyGraph>(this);
    }


}