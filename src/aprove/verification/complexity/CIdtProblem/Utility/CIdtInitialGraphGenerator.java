package aprove.verification.complexity.CIdtProblem.Utility;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.FreshVarGenerator;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Marcel Klinzing
 * copied from MPluecker
 */
public class CIdtInitialGraphGenerator {


    public Pair<IDependencyGraph, ImmutableSet<IEdge>> createInitialComplexityGraph(final ItpfFactory itpfFactory,
        final IDPPredefinedMap predefinedMap,
        final Collection<IRule> infRules,
        final Collection<IRule> rewriteRules,
        final IQTermSet q,
        final Abortion aborter) throws AbortionException {

        IDependencyGraph initialGraph =
            this.createInitialGraph(itpfFactory, predefinedMap, infRules, rewriteRules, false, q, aborter);

       Set<INode> initialNodes = new LinkedHashSet<INode>();
       for (Set<INode> nodes : initialGraph.getInitialRewriteNodes().values()) {
           initialNodes.addAll(nodes);
       }

       Set<IEdge> S = new LinkedHashSet<IEdge>();
       for (IEdge edge : initialGraph.getEdges()) {
           if (initialNodes.contains(edge.from) && edge.type.isInf()) {
               S.add(edge);
           }
       }

        Pair<IDependencyGraph, ImmutableSet<IEdge>> initialComplexityGraph = new Pair<IDependencyGraph, ImmutableSet<IEdge>>(
           initialGraph,
           ImmutableCreator.create(S));

        return initialComplexityGraph;
    }
    /**
     * @param itpfFactory
     * @param predefinedMap
     * @param rules
     * @param nonInfiniteRules (formally known as R)
     * @param q
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public IDependencyGraph createInitialGraph(final ItpfFactory itpfFactory,
        final IDPPredefinedMap predefinedMap,
        final Collection<IRule> infRules,
        final Collection<IRule> rewriteRules,
        final boolean minimal,
        final IQTermSet q,
        final Abortion aborter) throws AbortionException {

        final FreshNameGenerator freshNames =
            new FreshNameGenerator(new IDPNamesGenerator());

        final FreshVarGenerator freshVars = new FreshVarGenerator(freshNames);

        final PolyFactory polyFactory = itpfFactory.getPolyFactory();

        final InitialNodesResult initials =
            CIdtInitialGraphGenerator.createInitialNodes(infRules, rewriteRules, predefinedMap, itpfFactory, polyFactory, freshNames, aborter);

        final Map<INode, ITerm<?>> nodes = initials.nodes;
        final Map<INode, Itpf> nodeConditions =
            new LinkedHashMap<INode, Itpf>();
        for (final INode node : nodes.keySet()) {
            nodeConditions.put(node, itpfFactory.createTrue());
        }
        final Map<INode, VarRenaming> loopSubstitutions = initials.loopRenamings;
        final EdgeConditionMap edges = new EdgeConditionMap(itpfFactory, freshVars);
        for (final Map.Entry<IEdge, Itpf> edgeCondition : initials.edges.entrySet()) {
            edges.putReplace(edgeCondition.getKey(), edgeCondition.getValue());
        }

        final Map<IFunctionSymbol<?>, Set<IEdge>> ruleEdgeMap =
            this.generateRuleEdgeMap(nodes, edges);

        // create edges
        for (final IEdge ruleEdge : new ArrayList<IEdge>(edges.keySet())) {
            final INode fromNode = ruleEdge.to;
            final Set<IVariable<?>> unboundedVariables =
                new LinkedHashSet<IVariable<?>>(
                    nodes.get(fromNode).getVariables());
            unboundedVariables.removeAll(nodes.get(ruleEdge.from).getVariables());
            for (final Pair<IPosition, ITerm<?>> fromPos : nodes.get(fromNode).getPositionsWithSubTerms()) {
                if (!fromPos.y.isVariable()) {
                    final IFunctionApplication<?> fa =
                        (IFunctionApplication<?>) fromPos.y;
                    final Set<IEdge> succs =
                        ruleEdgeMap.get(fa.getRootSymbol());
                    if (succs != null) {
                        // we got a defined symbol here
                        for (final IEdge to : succs) {
                            final INode toNode = to.from;
                            final IFunctionApplication<?> toTerm =
                                (IFunctionApplication<?>) nodes.get(toNode);

                            Itpf formula;
                            if (fromNode == toNode) {
                                // do not wire this one!
                                continue;
                                // toTerm = toTerm.applySubstitution(loopSubstitutions.get(toNode));
                            }

                            final Set<ITerm<?>> S =
                                new LinkedHashSet<ITerm<?>>();

                            if (!toTerm.isVariable()) {
                                S.addAll(((IFunctionApplication<?>) toTerm).getArguments());
                            }
                            S.addAll(unboundedVariables);

                            final Map<ItpfAtom, Boolean> argFormulas =
                                new LinkedHashMap<ItpfAtom, Boolean>();

                            for (int i = 0; i < fa.getArguments().size(); i++) {
                                argFormulas.put(itpfFactory.createItp(
                                    fa.getArgument(i),
                                    RelDependency.Increasing,
                                    ItpfItp.EMPTY_CONTEXT,
                                    ItpRelation.TO_TRANS,
                                    toTerm.getArgument(i),
                                    RelDependency.Increasing,
                                    ItpfItp.EMPTY_CONTEXT), true);

                            }

                            formula =
                                itpfFactory.create(itpfFactory.createClause(
                                    ImmutableCreator.create(argFormulas),
                                    ImmutableCreator.create(ItpfUtil.expandS(S))));
                            edges.putOr(IEdge.create(fromNode, fromPos.x,
                                toNode, EdgeType.REWRITE), formula);
                            edges.putOr(IEdge.create(fromNode, fromPos.x,
                                toNode, EdgeType.INF), formula);
                        }
                    }
                }
            }
        }

        final IQTermSet cleanedQ = CIdtInitialGraphGenerator.renameQTerms(q, freshVars);

        return IDependencyGraph.create(predefinedMap,
            cleanedQ,
            itpfFactory,
            null,
            ImmutableCreator.create(nodes),
            ImmutableCreator.create(nodeConditions),
            ImmutableCreator.create(initials.initialNodes),
            IDependencyGraph.createEmptyNodeUnrollCounter(nodes.keySet()),
            ImmutableCreator.create(loopSubstitutions),
            ImmutableCreator.create(edges.getMap()),
            freshVars);
    }

    private Map<IFunctionSymbol<?>, Set<IEdge>> generateRuleEdgeMap(final Map<INode, ITerm<?>> nodes,
        final EdgeConditionMap ruleEdges) {
        final Map<IFunctionSymbol<?>, Set<IEdge>> res =
            new LinkedHashMap<IFunctionSymbol<?>, Set<IEdge>>();
        for (final IEdge edge : ruleEdges.keySet()) {
            final INode fromNode = edge.from;
            final ITerm<?> fromTerm = nodes.get(fromNode);
            if (!fromTerm.isVariable()) {
                final IFunctionSymbol<?> root =
                    ((IFunctionApplication<?>) fromTerm).getRootSymbol();
                Set<IEdge> nds = res.get(root);
                if (nds == null) {
                    nds = new LinkedHashSet<IEdge>();
                    res.put(root, nds);
                }
                nds.add(edge);
            }
        }
        return res;
    }

    /**
     * @param nonInfiniteRules
     * @param freshNames
     * @param ruleAnalysis
     * @param aborter
     * @param predefinedMap
     * @return x: node-> term, y: node->loopSubstitution, z: terms of nodes
     * which for a rules
     */
    public static InitialNodesResult createInitialNodes(final Collection<IRule> infRules,
        final Collection<IRule> rewriteRules, final IDPPredefinedMap predefinedMap,
        final ItpfFactory itpfFactory,
        final PolyFactory polyFactory,
        final FreshNameGenerator freshNames,
        final Abortion aborter) {

        final Set<IVariable<?>> lockedVars = new LinkedHashSet<IVariable<?>>();
        final Map<INode, ITerm<?>> nodes = new LinkedHashMap<INode, ITerm<?>>();
        final Set<INode> initialNodes = new LinkedHashSet<INode>();
        final Map<ITerm<?>, INode> termsToNodes =
            new HashMap<ITerm<?>, INode>();
        final Map<IEdge, Itpf> ruleEdges =
            new LinkedHashMap<IEdge, Itpf>(infRules.size() + rewriteRules.size());
        int maxNodeId = -1;
        final Map<INode, VarRenaming> loopSubstitutions =
            new LinkedHashMap<INode, VarRenaming>();

        final LinkedHashSet<IRule> allRules = new LinkedHashSet<IRule>(infRules);
        allRules.addAll(rewriteRules);

        for (final IRule rule : allRules) {
            INode lhsNode =
                termsToNodes.get(rule.getLhsInStandardRepresentation());
            final PolyTermSubstitution lhsMatcher;
            if (lhsNode == null) {
                final int lhsNodeIdL = ++maxNodeId;
                lhsNode = INode.create(lhsNodeIdL);
                final Pair<Map<IVariable<?>, IVariable<?>>, Map<IVariable<?>, IVariable<?>>> lhsSubst =
                    CIdtInitialGraphGenerator.createTermSubst(freshNames, lockedVars, rule.getLeft(),
                        lhsNodeIdL);
                loopSubstitutions.put(lhsNode, VarRenaming.create(
                    ImmutableCreator.create(lhsSubst.y), true, polyFactory));
                final VarRenaming lhsRename =
                    VarRenaming.create(ImmutableCreator.create(lhsSubst.x),
                        true, polyFactory);
                nodes.put(lhsNode, rule.getLeft().applySubstitution(lhsRename));
                termsToNodes.put(rule.getLhsInStandardRepresentation(), lhsNode);
                lhsMatcher = lhsRename;
            } else {
                lhsMatcher = TermToPolyTermSubstitution.create(rule.getLeft().getMatcher(nodes.get(lhsNode)), predefinedMap, null);
            }
            // RHS
            INode rhsNode =
                termsToNodes.get(rule.getRhsInStandardRepresentation());
            final PolyTermSubstitution rhsMatcher;
            final int rhsNodeId = ++maxNodeId;
            if (rhsNode == null) {
                rhsNode = INode.create(rhsNodeId);
                final Pair<Map<IVariable<?>, IVariable<?>>, Map<IVariable<?>, IVariable<?>>> rhsSubst =
                    CIdtInitialGraphGenerator.createTermSubst(freshNames, lockedVars, rule.getRight(),
                        rhsNodeId);
                loopSubstitutions.put(rhsNode, VarRenaming.create(
                    ImmutableCreator.create(rhsSubst.y), true, polyFactory));
                final VarRenaming rhsRename =
                    VarRenaming.create(ImmutableCreator.create(rhsSubst.x),
                        true, polyFactory);
                nodes.put(rhsNode, rule.getRight().applySubstitution(rhsRename));
                termsToNodes.put(rule.getRhsInStandardRepresentation(), rhsNode);
                rhsMatcher = rhsRename;
            } else {
                ITerm<?> rhsTerm = nodes.get(rhsNode);
                if (lhsNode == rhsNode) {
                    rhsTerm =
                        rhsTerm.applySubstitution(loopSubstitutions.get(rhsNode));
                }
                rhsMatcher = TermToPolyTermSubstitution.create(rule.getRight().getMatcher(rhsTerm), predefinedMap, null);
            }

            Itpf condition;
            if (rule.getCondition() != null) {
                condition = CIdtInitialGraphGenerator.renameBoundVars(rule.getCondition(), rhsNodeId, itpfFactory, freshNames).applySubstitution(lhsMatcher).applySubstitution(
                    rhsMatcher);
            } else {
                condition = itpfFactory.createTrue();
            }

            final Map<ItpfAtom, Boolean> unifications =
                new LinkedHashMap<ItpfAtom, Boolean>();
            final Set<IVariable<?>> lhsVars = rule.getLeft().getVariables();
            final Set<IVariable<?>> rhsVars = rule.getRight().getVariables();
            final LinkedHashSet<ITerm<?>> S = new LinkedHashSet<ITerm<?>>();

            for (final ITerm<?> leftArg : rule.getLeft().getArguments()) {
                S.add(leftArg.applySubstitution(lhsMatcher));
            }

            for (final IVariable<?> var : rule.getVariables()) {
                if (lhsVars.contains(var) && rhsVars.contains(var)) {
                    final ITerm<?> matchedLhsVar =
                        var.applySubstitution(lhsMatcher);
                    final ITerm<?> matchedRhsVar =
                        var.applySubstitution(rhsMatcher);

                    S.add(matchedLhsVar);
                    S.add(matchedRhsVar);

                    unifications.put(itpfFactory.createItp(matchedLhsVar,
                        RelDependency.Increasing,
                        ItpfItp.EMPTY_CONTEXT, ItpRelation.EQ,
                        matchedRhsVar, RelDependency.Increasing,
                        ItpfItp.EMPTY_CONTEXT), true);
                }
            }
            condition =
                itpfFactory.createAnd(condition,
                    itpfFactory.create(itpfFactory.createClause(
                        ImmutableCreator.create(unifications),
                        ImmutableCreator.create(ItpfUtil.expandS(S)))));

            if (rewriteRules.contains(rule)) {
                ruleEdges.put(IEdge.create(lhsNode, IPosition.create(), rhsNode,
                    EdgeType.REWRITE), condition);
            }

            if (infRules.contains(rule)) {
                ruleEdges.put(IEdge.create(lhsNode, IPosition.create(), rhsNode,
                    EdgeType.INF), condition);
            }

            initialNodes.add(lhsNode);
        }
        return new InitialNodesResult(
            nodes, loopSubstitutions, initialNodes, ruleEdges);
    }

    private static Itpf renameBoundVars(final Itpf condition, final int nodeId,
        final ItpfFactory itpfFactory,
        final FreshNameGenerator freshNames) {
        final Map<IVariable<?>, IVariable<?>> renaming = new LinkedHashMap<IVariable<?>, IVariable<?>>();

        for (final IVariable<?> var : condition.getBoundVariables()) {
            final String newName = freshNames.getFreshName(var.getName() + "_" + nodeId, false);
            renaming.put(var, IVariable.create(newName, var.getDomain()));
        }

        final PolyTermSubstitution boundVarsRenaming = VarRenaming.create(ImmutableCreator.create(renaming), true, itpfFactory.getPolyFactory());

        return condition.applySubstitution(boundVarsRenaming, true);
    }

    // term (substitution, loopSubstitution)
    static Pair<Map<IVariable<?>, IVariable<?>>, Map<IVariable<?>, IVariable<?>>> createTermSubst(final FreshNameGenerator freshNames,
        final Set<IVariable<?>> lockedVars,
        final ITerm<?> term,
        final int newNodeId) {
        final Set<IVariable<?>> termVars = term.getVariables();
        final Map<IVariable<?>, IVariable<?>> subst =
            new LinkedHashMap<IVariable<?>, IVariable<?>>();
        final Map<IVariable<?>, IVariable<?>> loopSubst =
            new LinkedHashMap<IVariable<?>, IVariable<?>>();
        for (final IVariable<?> v : termVars) {
            final String newName =
                freshNames.getFreshName(v.getName() + "_" + newNodeId, false);
            IVariable<?> newVar;
            if (!newName.equals(v.getName())) {
                newVar = ITerm.createVariable(newName, v.getDomain());
                lockedVars.add(newVar);
                subst.put(v, newVar);
            } else {
                newVar = v;
                lockedVars.add(v);
            }
            {
                final String newLoopName =
                    freshNames.getFreshName(newName, false);
                final IVariable<?> newLoopVar =
                    ITerm.createVariable(newLoopName, v.getDomain());
                lockedVars.add(newLoopVar);
                loopSubst.put(newVar, newLoopVar);
            }
        }
        return new Pair<Map<IVariable<?>, IVariable<?>>, Map<IVariable<?>, IVariable<?>>>(
            subst, loopSubst);
    }

    static IQTermSet renameQTerms(final IQTermSet q, final FreshVarGenerator freshVars) {
        final Set<IFunctionApplication<?>> renamedQTerms = new LinkedHashSet<IFunctionApplication<?>>();

        for (final IFunctionApplication<?> qTerm : q.getUserDefinedTerms()) {
            renamedQTerms.add(qTerm.renameVariables(freshVars));
        }

        return new IQTermSet(ImmutableCreator.create(renamedQTerms), q.getPredefinedMode(), q.getPredefinedMap());
    }

    private static class InitialNodesResult {

        final Map<INode, ITerm<?>> nodes;
        final Map<INode, VarRenaming> loopRenamings;
        final Set<INode> initialNodes;
        final Map<IEdge, Itpf> edges;

        public InitialNodesResult(final Map<INode, ITerm<?>> nodes, final Map<INode, VarRenaming> loopRenamings, final Set<INode> initialNodes, final Map<IEdge, Itpf> edges) {
            this.nodes = nodes;
            this.loopRenamings = loopRenamings;
            this.initialNodes = initialNodes;
            this.edges = edges;
        }

    }
}
