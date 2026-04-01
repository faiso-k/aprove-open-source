/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.idpGraph;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.Processors.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.cap.*;
import aprove.verification.dpframework.IDPProblem.Processors.processorHistory.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class IDependencyGraph implements Immutable, IIDependencyGraph {

    public static IDependencyGraph create(RuleAnalysis<GeneralizedRule> nodeAnalysis, ImmutableSet<Node> nodes, ImmutableSet<IdpEdge> edges, int maxNodeId, ImmutableSet<TRSVariable> lockedVars, IDPProcessor proc) {
        return IDependencyGraph.create(nodeAnalysis, nodes, edges, YNM.MAYBE, maxNodeId, lockedVars, proc);
    }

    public static IDependencyGraph create(RuleAnalysis<GeneralizedRule> nodeAnalysis, ImmutableSet<Node> nodes, ImmutableSet<IdpEdge> edges, YNM isSCC, int maxNodeId, ImmutableSet<TRSVariable> lockedVars, IDPProcessor proc) {
        if (aprove.Globals.useAssertions) {
            IDependencyGraph.checkNodes(nodeAnalysis, nodes, maxNodeId, lockedVars);
            IDependencyGraph.checkEdges(nodes, edges);
        }
        return new IDependencyGraph(nodeAnalysis, nodes, edges, null, null, isSCC, IdpProcessorHistory.initialHistory(proc), maxNodeId, lockedVars);
    }

    protected static void checkEdges(Set<Node> nodes, Set<IdpEdge> edges) {
        Iterator<IdpEdge> i = edges.iterator();
        while(i.hasNext()) {
            IdpEdge edge = i.next();
            Node from = edge.getFrom();
            Node to = edge.getTo();
            assert(nodes.contains(from) && nodes.contains(to)) : "invalid edge : " + edge;
        }
    }

    protected static void checkNodes(RuleAnalysis<GeneralizedRule> nodeAnalysis, Set<Node> nodes, int maxNodeId, ImmutableSet<TRSVariable> lockedVars) {
        Set<TRSVariable> used = new HashSet<TRSVariable>();
        Set<GeneralizedRule> nodeRules = new HashSet<GeneralizedRule>();
        ImmutableSet<GeneralizedRule> rules = nodeAnalysis.getRules();
        for (Node n : nodes) {
            Set<TRSVariable> nodeVars = n.rule.getVariables();
            assert(rules.contains(n.rule));
            for (TRSVariable v : nodeVars) {
                assert(used.add(v)) : "Nodes not variable disjoint";
            }
            nodeRules.add(n.rule);
            assert(n.id <= maxNodeId) : "MaxNodeId invalid.";
            if (lockedVars != null) {
                assert(lockedVars.containsAll(n.rule.getVariables())) : "vars not locked";
            }
        }
        assert(nodeRules.containsAll(rules)) : "Nodes do not cover all rules";
    }

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
     * Integer constant representing the toInteractiveDOTwithEdges()
     * method.
     */
    protected static final int INTERACTIVE = 3;

    /**
     * Integer constant representing the toDOTDOT() method.
     */
    protected static final int DOTDOT1 = 4;

    /**
     * Integer constant representing the
     * toDOTDOT(boolean,float,float,boolean) method.
     */
    protected static final int DOTDOT2 = 5;

    private final RuleAnalysis<GeneralizedRule> nodeAnalysis;
    private final Integer maxNodeId;
    private final ImmutableSet<TRSVariable> lockedVars;
    private final ImmutableSet<Node> nodes;
    private final ImmutableSet<IdpEdge> edges;
    private volatile ImmutableMap<Node, ImmutableMap<Node, IdpEdge>> post;
    private volatile ImmutableMap<Node, ImmutableMap<Node, IdpEdge>> pre;
    private volatile ImmutableList<ImmutableSet<Node>> sccs;

    private final IdpProcessorHistory procHistory;
    private final YNM isSCC;


    private IDependencyGraph(
            RuleAnalysis<GeneralizedRule> nodeAnalysis,
            ImmutableSet<Node> nodes,
            ImmutableSet<IdpEdge> edges,
            ImmutableMap<Node, ImmutableMap<Node, IdpEdge>> pre,
            ImmutableMap<Node, ImmutableMap<Node, IdpEdge>> post,
            YNM isSCC, IdpProcessorHistory procHistory,
            Integer maxNodeId, ImmutableSet<TRSVariable> lockedVars) {
        this.nodeAnalysis = nodeAnalysis;
        this.nodes = nodes;
        this.edges = edges;
        this.procHistory = procHistory;
        this.isSCC = isSCC;
        this.pre = pre;
        this.post = post;
        this.maxNodeId = maxNodeId;
        this.lockedVars = lockedVars;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.IDPProblem.idpGraph.IIdependencyGraph#getNodes()
     */
    @Override
    public ImmutableSet<Node> getNodes() {
        return this.nodes;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.IDPProblem.idpGraph.IIdependencyGraph#getEdges()
     */
    @Override
    public ImmutableSet<IdpEdge> getEdges() {
        return this.edges;
    }

    @Override
    public RuleAnalysis<GeneralizedRule> getNodeAnalysis() {
        return this.nodeAnalysis;
    }

    @Override
    public IdpProcessorHistory getProcHistory() {
        return this.procHistory;
    }

    @Override
    public YNM isSCC() {
        return this.isSCC;
    }


    /*
    public IIDependencyGraph renameNodes(Map<Node, Node> nodeRenaming,
            IDPProcessor proc) {
        if (graph != null) {
            Map<Node, ImmutableSet<IdpEdge>> newGraph = new LinkedHashMap<Node, ImmutableSet<IdpEdge>>();
            for (Map.Entry<Node, ImmutableSet<IdpEdge>> entry : graph.entrySet()) {
                Node newNode = nodeRenaming.get(entry.getKey());
                if (newNode == null) {
                    newNode = entry.getKey();
                }
                Set<IdpEdge> newEdges = new LinkedHashSet<IdpEdge>();
                for (IdpEdge edge : entry.getValue()) {
                    edge.change(from, to, itpf, proc)
                }
            }

        } else {

        }
    }*/

    @Override
    public IIDependencyGraph changeLabels(Map<IdpEdge, Itpf> newFormulas,
            IDPProcessor proc) {
        Set<IdpEdge> newEdges = new LinkedHashSet<IdpEdge> (this.edges);
        boolean removedEdge = false;
        for (Map.Entry<IdpEdge, Itpf> newEntry : newFormulas.entrySet()) {
            if (newEdges.remove(newEntry.getKey())) {
                if (!Itpf.FALSE.equals(newEntry.getValue())) {
                    newEdges.add(newEntry.getKey().change(null, null, newEntry.getValue(), proc));
                } else {
                    removedEdge = true;
                }
            }
        }
        return new IDependencyGraph(this.nodeAnalysis, this.nodes, ImmutableCreator.create(newEdges), null, null, removedEdge ? YNM.MAYBE : this.isSCC, IdpProcessorHistory.newEntry(this.procHistory, proc), this.maxNodeId, this.lockedVars);
    }


    @Override
    public IIDependencyGraph restrictToSccs(IDPProcessor proc) {
        ImmutableList<ImmutableSet<Node>> sccs = this.getSCCs();
        Set<Node> remove = new LinkedHashSet<Node>(this.getNodes());
        for (ImmutableSet<Node> scc : sccs) {
            remove.removeAll(scc);
        }
        IDependencyGraph newGraph = (IDependencyGraph) this.removeNodes(remove, YNM.YES, proc);
        newGraph.sccs = sccs;
        return newGraph;
    }

    @Override
    public IDependencyGraph removeNodes(Set<Node> remove, YNM isSCC,
            IDPProcessor proc) {
        Set<Node> newNodes = new LinkedHashSet<Node>(this.nodes);
        newNodes.removeAll(remove);
        return this.restrictToNodes(ImmutableCreator.create(newNodes), isSCC, proc);
    }

    @Override
    public IDependencyGraph restrictToNodes(RuleAnalysis<GeneralizedRule> ruleAnalysis,
            Set<Node> newNodes, YNM isSCC, IDPProcessor proc) {
        Set<Node> nn = new LinkedHashSet<Node>(this.nodes);
        nn.retainAll(this.nodes);
        if (Globals.useAssertions) {
            IDependencyGraph.checkNodes(ruleAnalysis, nn, this.maxNodeId, null);
        }
        return this.uncheckedRestrictToNodes(ruleAnalysis, ImmutableCreator.create(nn), isSCC, proc);
    }

    @Override
    public IDependencyGraph restrictToNodes(Set<Node> newNodes, YNM isSCC,
            IDPProcessor proc) {
        Set<Node> nn = new LinkedHashSet<Node>(newNodes);
        nn.retainAll(this.nodes);

        Set<GeneralizedRule> newRules = new LinkedHashSet<GeneralizedRule>();
        for (Node n : nn) {
            newRules.add(n.rule);
        }
        return this.uncheckedRestrictToNodes(new RuleAnalysis<GeneralizedRule>(ImmutableCreator.create(newRules), this.nodeAnalysis.getPreDefinedMap()), ImmutableCreator.create(nn), isSCC, proc);
    }

    protected IDependencyGraph uncheckedRestrictToNodes(RuleAnalysis<GeneralizedRule> nodeAnalysis, ImmutableSet<Node> newNodes, YNM isSCC,
            IDPProcessor proc) {
        if (isSCC == null) {
            isSCC = YNM.MAYBE;
        }
        this.buildPrePost();
        Set<IdpEdge> newEdges = new LinkedHashSet<IdpEdge>();
        Map<Node, ImmutableMap<Node, IdpEdge>> preImmu = this.restrictPrePostMap(this.pre, newNodes, newEdges);
        Map<Node, ImmutableMap<Node, IdpEdge>> postImmu = this.restrictPrePostMap(this.post, newNodes, null);
        return new IDependencyGraph(nodeAnalysis, newNodes, ImmutableCreator.create(newEdges), ImmutableCreator.create(preImmu), ImmutableCreator.create(postImmu), isSCC, IdpProcessorHistory.newEntry(this.procHistory, proc), this.maxNodeId, this.lockedVars);
    }

    protected Map<Node, ImmutableMap<Node, IdpEdge>> restrictPrePostMap(Map<Node, ImmutableMap<Node, IdpEdge>> map, ImmutableSet<Node> newNodes, Set<IdpEdge> fillEdges) {
        Map<Node, ImmutableMap<Node, IdpEdge>> res = new LinkedHashMap<Node, ImmutableMap<Node, IdpEdge>>();
        for (Map.Entry<Node, ImmutableMap<Node, IdpEdge>> entry : map.entrySet()) {
            if (newNodes.contains(entry.getKey())) {
                Map<Node, IdpEdge> nodeMap = new LinkedHashMap<Node, IdpEdge>();
                for (Map.Entry<Node, IdpEdge> succEntry : entry.getValue().entrySet()) {
                    if (newNodes.contains(succEntry.getKey())) {
                        nodeMap.put(succEntry.getKey(), succEntry.getValue());
                        if (fillEdges != null) {
                            fillEdges.add(succEntry.getValue());
                        }
                    }
                }
                res.put(entry.getKey(), ImmutableCreator.create(nodeMap));
            }
        }
        return res;
    }

    @Override
    public ImmutableList<IIDependencyGraph> splitIntoSCCs(IDPProcessor proc) {
        if (this.isSCC == YNM.YES) {
            return ImmutableCreator.create(Collections.<IIDependencyGraph>singletonList(this));
        }
        ImmutableList<ImmutableSet<Node>> sccs = this.getSCCs();
        List<IIDependencyGraph> tmp = new ArrayList<IIDependencyGraph>(sccs.size());
        for (ImmutableSet<Node> scc : sccs) {
            tmp.add(this.restrictToNodes(scc, YNM.YES, proc));
        }
        return ImmutableCreator.create(tmp);
    }

    @Override
    public IIDependencyGraph collapseNode(IDPRuleAnalysis ruleAnalysis, Node node,
            IDPProcessor proc) {
        return this.collapseNodes(ruleAnalysis, Collections.singleton(node), IECap.Estimation.getEstimation(IECap.Estimation.DEFAULT), proc);
    }

    @Override
    public IIDependencyGraph collapseNode(IDPRuleAnalysis ruleAnalysis, Node node,
            IECap cap, IDPProcessor proc) {
        return this.collapseNodes(ruleAnalysis, Collections.singleton(node), cap, proc);
    }

    @Override
    public IIDependencyGraph collapseNodes(IDPRuleAnalysis ruleAnalysis, Collection<Node> nodes, IDPProcessor proc) {
        return this.collapseNodes(ruleAnalysis, nodes, IECap.Estimation.getEstimation(IECap.Estimation.DEFAULT), proc);
    }

    @Override
    public IIDependencyGraph collapseNodes(IDPRuleAnalysis ruleAnalysis, Collection<Node> nodes, IECap cap, IDPProcessor proc) {
        if (Globals.useAssertions) {
            Set<GeneralizedRule> rules = new LinkedHashSet<GeneralizedRule>(this.nodeAnalysis.getRules());
            for (Node node : nodes) {
                assert(rules.remove(node.rule));
            }
            assert(rules.equals(ruleAnalysis.getPAnalysis().getRules()));
        }
        return this.uncheckedCollapseNodes(ruleAnalysis, nodes, cap, proc);
    }

    protected IIDependencyGraph uncheckedCollapseNodes(IDPRuleAnalysis ruleAnalysis, Collection<Node> collapseNodes, IECap cap, IDPProcessor proc) {
        this.buildPrePost();
        Set<TRSVariable> usedVars = new LinkedHashSet<TRSVariable>();
        for (Node node : this.nodes) {
            usedVars.addAll(node.rule.getVariables());
            usedVars.addAll(node.loopSubstitution.values());
        }
        System.err.println("MY NODES: " + this.nodes);
        Set<Node> newNodes = new LinkedHashSet<Node>(this.nodes);
        if (!newNodes.removeAll(collapseNodes)) {
            return new IDependencyGraph(this.nodeAnalysis, this.nodes, this.edges, this.pre, this.post, this.isSCC, IdpProcessorHistory.newEntry(this.procHistory, proc), this.maxNodeId, this.lockedVars);
        }
        System.err.println("COLLAPSE NODES: " + collapseNodes);
        System.err.println("NEW NODES: " + newNodes);
        Set<IdpEdge> newEdges = new LinkedHashSet<IdpEdge>(this.edges);
        Map<Node, Map<Node, IdpEdge>> newPre = new LinkedHashMap<Node, Map<Node, IdpEdge>>(this.pre);
        Map<Node, Map<Node, IdpEdge>> newPost = new LinkedHashMap<Node, Map<Node, IdpEdge>>(this.post);
        IECap.ICapFreshNameGenerator capFreshNames = new IECap.CapFreshNameGenerator();
        FreshNameGenerator freshVars = new FreshNameGenerator(this.lockedVars, FreshNameGenerator.VARIABLES);
        Set<TRSVariable> newLockedVars = new LinkedHashSet<TRSVariable>(this.lockedVars);
        int newMaxNodeId = this.maxNodeId;
        for (Node node : collapseNodes) {
            Map<Node, IdpEdge> predecs = newPre.remove(node);
            Map<Node, IdpEdge> succs = newPost.remove(node);
            for (Map.Entry<Node, IdpEdge> predecE : predecs.entrySet()) {
                IdpEdge preEdge = predecE.getValue();
                Node predec = predecE.getKey();
                newEdges.remove(preEdge);
                System.err.println("REMOVE EDGE: " + preEdge.getFrom().id + " " + preEdge.getTo().id);
                if (predec == node) {
                    throw new IllegalArgumentException("node has a self-loop");
                }
                Map<Node, IdpEdge> predecPostMap = newPost.get(predec);
                if (predecPostMap instanceof Immutable) {
                    predecPostMap = new LinkedHashMap<Node, IdpEdge>(predecPostMap);
                    newPost.put(predec, predecPostMap);
                    predecPostMap.remove(node);
                }

                // generate new node
                Set<TRSTerm> s = new LinkedHashSet<TRSTerm>();
                s.add(predec.rule.getLeft());
                s.add(node.rule.getLeft());
                s.addAll(predec.rule.getUnboundedVariables());
                s.addAll(node.rule.getUnboundedVariables());
                TRSTerm cappedPredecRight = cap.cap(ruleAnalysis, s, predec.rule.getRight(), capFreshNames, false, false).x;
                TRSSubstitution mgu = node.rule.getLeft().getMGU(cappedPredecRight);
                if (mgu == null) {
                    continue;
                }
                TRSFunctionApplication newLeft = predec.rule.getLeft().applySubstitution(mgu);
                TRSTerm newRight = node.rule.getRight().applySubstitution(mgu);
                Map<TRSVariable, TRSVariable> varDisjointMap = new LinkedHashMap<TRSVariable, TRSVariable>();
                Map<TRSVariable, TRSVariable> loopSubst = new LinkedHashMap<TRSVariable, TRSVariable>();
                Set<TRSVariable> variables = newRight.getVariables();
                variables.addAll(newLeft.getVariables());
                for (TRSVariable var : variables) {
                    String newName = freshVars.getFreshName(var.getName(), false);
                    TRSVariable newVar;
                    if (!newName.equals(var.getName())) {
                        newVar = TRSTerm.createVariable(newName);
                        newLockedVars.add(newVar);
                        varDisjointMap.put(var, newVar);
                    } else {
                        newVar = var;
                    }
                    newName = freshVars.getFreshName(newName, false);
                    if (!newName.equals(var.getName())) {
                        TRSVariable newLoopVar = TRSTerm.createVariable(newName);
                        newLockedVars.add(newLoopVar);
                        loopSubst.put(newVar, newLoopVar);
                    }
                }
                TRSSubstitution varRenamed = TRSSubstitution.create(ImmutableCreator.create(varDisjointMap), true);
                newLeft = newLeft.applySubstitution(varRenamed);
                newRight = newRight.applySubstitution(varRenamed);
                GeneralizedRule newRule = GeneralizedRule.create(newLeft, newRight);
                Node newNode = new Node(
                        newRule,
                        ++newMaxNodeId,
                        ImmutableCreator.create(loopSubst));
                newNodes.add(newNode);
                Map<Node, IdpEdge> newNodePre = new LinkedHashMap<Node, IdpEdge>();
                newPre.put(newNode, newNodePre);
                // all predecessors of predec are predecessors of newNode
                for (Map.Entry<Node, IdpEdge> predecPreEntry : newPre.get(predec).entrySet()) {
                    if (predecPreEntry.getKey() != node) {
                        // new Self-Loops are handled in post section
                        Itpf formula =  predecPreEntry.getValue().getItpf();
                        formula = formula.applySubstitution(mgu);
                        formula = formula.applySubstitution(varRenamed);
                        IdpEdge newEdge = predecPreEntry.getValue().change(predecPreEntry.getKey(), newNode, formula, proc);
                        newEdges.add(newEdge);
                        System.err.println("ADD EDGE: " + newEdge.getFrom().id + " " + newEdge.getTo().id);
                        newNodePre.put(predecPreEntry.getKey(), newEdge);
                        Map<Node, IdpEdge> prepreSuccMap = newPost.get(predecPreEntry.getKey());
                        if (prepreSuccMap instanceof Immutable) {
                            prepreSuccMap = new LinkedHashMap<Node, IdpEdge>(prepreSuccMap);
                            newPost.put(predecPreEntry.getKey(), prepreSuccMap);
                        }
                        prepreSuccMap.put(newNode, newEdge);
                    }
                }
                Map<Node, IdpEdge> newNodePost = new LinkedHashMap<Node, IdpEdge>();
                newPost.put(newNode, newNodePost);

                for (Map.Entry<Node, IdpEdge> succE : succs.entrySet()) {
                    IdpEdge succEdge = succE.getValue();
                    Node succ = succE.getKey();
                    if (succ == node) {
                        throw new IllegalArgumentException("node has a self-loop");
                    }

                    Itpf succFormula = succEdge.getItpf();
                    if (predec == succ) {
                        // protect variables of succ node
                        succFormula = succFormula.applySubstitution(TRSSubstitution.create(succ.loopSubstitution, true));
                    }
                    succFormula = succFormula.applySubstitution(mgu);
                    succFormula = succFormula.applySubstitution(varRenamed);
                    Itpf formula = ItpfAnd.create(preEdge.getItpf().applySubstitution(mgu).applySubstitution(varRenamed), succFormula);
                    if (predec == succ) {
                        // undo protection of variables of succ node
                        Map<TRSVariable, TRSVariable> inverted = new LinkedHashMap<TRSVariable, TRSVariable>();
                        for (Map.Entry<TRSVariable, TRSVariable> e : succ.loopSubstitution.entrySet()) {
                            inverted.put(e.getValue(), e.getKey());
                        }
                        Itpf protectedFormula = formula;
                        formula = protectedFormula.applySubstitution(TRSSubstitution.create(ImmutableCreator.create(inverted), true));

                        // handle self-loop
                        Map<TRSVariable, TRSTerm> loopReplace = new LinkedHashMap<TRSVariable, TRSTerm>(inverted);
                        TRSSubstitution newNodeLoopRename = TRSSubstitution.create(newNode.loopSubstitution);
                        for (Map.Entry<TRSVariable, TRSTerm> e : loopReplace.entrySet()) {
                            e.setValue(e.getValue().applySubstitution(mgu).applySubstitution(varRenamed).applySubstitution(newNodeLoopRename));
                        }
                        Itpf selfLoopFormula = protectedFormula.applySubstitution(TRSSubstitution.create(ImmutableCreator.create(loopReplace), true));
                        Set<TRSVariable> selfQuantVars = new LinkedHashSet<TRSVariable>(selfLoopFormula.getFreeVariables());
                        selfQuantVars.removeAll(newNode.rule.getVariables());
                        selfQuantVars.removeAll(newNode.loopSubstitution.values());
                        selfLoopFormula =  ItpfUtils.quantifyExist(selfQuantVars, selfLoopFormula);
                        selfLoopFormula = selfLoopFormula.normalize();
                        IdpEdge selfEdge = succEdge.change(newNode, newNode, selfLoopFormula, proc);
                        newEdges.add(selfEdge);
                        newNodePre.put(newNode, selfEdge);
                        newNodePost.put(newNode, selfEdge);
                    }
                    Set<TRSVariable> quantVars = new LinkedHashSet<TRSVariable>(formula.getFreeVariables());
                    quantVars.removeAll(newNode.rule.getRight().getVariables());
                    quantVars.removeAll(succ.rule.getLeft().getVariables());
                    formula =  ItpfUtils.quantifyExist(quantVars, formula);
                    formula = formula.normalize();
                    IdpEdge newEdge;
                    newEdge = succEdge.change(newNode, succ, formula, proc);
                    newEdges.add(newEdge);
                    Map<Node, IdpEdge> succPreMap = newPre.get(succ);
                    if (succPreMap instanceof Immutable) {
                        succPreMap = new LinkedHashMap<Node, IdpEdge>(succPreMap);
                        newPre.put(succ, succPreMap);
                    }
                    succPreMap.put(predec, newEdge);
                    newNodePost.put(succ, newEdge);
                    predecPostMap.put(succ, newEdge);
                    System.err.println("ADD EDGE: " + newEdge.getFrom().id + " " + newEdge.getTo().id);
                }
            }
            for (Map.Entry<Node, IdpEdge> succE : succs.entrySet()) {
                IdpEdge succEdge = succE.getValue();
                Node succ = succE.getKey();
                newEdges.remove(succEdge);
                System.err.println("REMOVE EDGE: " + succEdge.getFrom().id + " " + succEdge.getTo().id);

                Map<Node, IdpEdge> succPreMap = newPre.get(succ);
                if (succPreMap instanceof Immutable) {
                    succPreMap = new LinkedHashMap<Node, IdpEdge>(succPreMap);
                    newPre.put(succ, succPreMap);
                }
                succPreMap.remove(node);
            }
        }
        System.err.println("newPost: " + newPost);
        Map<Node, ImmutableMap<Node, IdpEdge>> preImmu = new LinkedHashMap<Node, ImmutableMap<Node, IdpEdge>>();
        Map<Node, ImmutableMap<Node, IdpEdge>> postImmu = new LinkedHashMap<Node, ImmutableMap<Node, IdpEdge>>();
        for (Map.Entry<Node, Map<Node, IdpEdge>> entry : newPre.entrySet()) {
            preImmu.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
        }
        for (Map.Entry<Node, Map<Node, IdpEdge>> entry : newPost.entrySet()) {
            postImmu.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
        }

        return new IDependencyGraph(this.nodeAnalysis, ImmutableCreator.create(newNodes), ImmutableCreator.create(newEdges), ImmutableCreator.create(preImmu), ImmutableCreator.create(postImmu), this.isSCC, IdpProcessorHistory.newEntry(this.procHistory, proc), newMaxNodeId, ImmutableCreator.create(newLockedVars));
    }



    @Override
    public boolean containsEdge(Node from, Node to) {
        this.buildPrePost();
        ImmutableMap<Node, IdpEdge> posts = this.post.get(from);
        if (posts != null) {
            return posts.containsKey(to);
        } else {
            return false;
        }
    }


    @Override
    public int getInDegree(Node node) {
        this.buildPrePost();
        return this.pre.get(node).size();
    }

    @Override
    public int getOutDegree(Node node) {
        this.buildPrePost();
        return this.post.get(node).size();
    }

    @Override
    public ImmutableMap<Node, IdpEdge> getPredecessors(Node node) {
        this.buildPrePost();
        return this.pre.get(node);
    }

    @Override
    public ImmutableMap<Node, IdpEdge> getSuccessors(Node node) {
        this.buildPrePost();
        return this.post.get(node);
    }

    @Override
    public IdpEdge getEdge(Node from, Node to) {
        this.buildPrePost();
        ImmutableMap<Node, IdpEdge> posts = this.post.get(from);
        /*
        System.err.println("Post: " + from.id + " -> " + to.id);
        for (Map.Entry<Node, IdpEdge> e : posts.entrySet()) {
            System.err.println("Succs: " + e.getKey().id);
        }*/
        if (posts != null) {
            IdpEdge res = posts.get(to);
            return res;
        } else {
            return null;
        }
    }

    @Override
    public Itpf itpfPath(VariableRenamedPath path) {
        if (path.getPath().size() < 2) {
            return Itpf.TRUE;
        }
        Set<Itpf> conj = new LinkedHashSet<Itpf>();
        Iterator<ImmutablePair<Node, ImmutableMap<TRSVariable, TRSVariable>>> iter = path.getPath().iterator();
        ImmutablePair<Node, ImmutableMap<TRSVariable, TRSVariable>> current = iter.next();
        while (iter.hasNext()) {
            ImmutablePair<Node, ImmutableMap<TRSVariable, TRSVariable>> next = iter.next();
            Map<TRSVariable, TRSVariable> combined = new LinkedHashMap<TRSVariable, TRSVariable>(current.y);
            if (current.x == next.x) {
                // loop -> concern about loop renaming
                for (Map.Entry<TRSVariable, ? extends TRSTerm> ren : current.x.loopSubstitution.entrySet()) {
                    TRSVariable from = (TRSVariable) ren.getValue();
                    TRSVariable to = next.y.get(ren.getKey());
                    if (to == null) {
                        to = ren.getKey();
                    }
                    if (!from.equals(to)) {
                        combined.put(from, to);
                    }
                }
            } else {
                combined.putAll(next.y);
            }
            conj.add(this.getEdge(current.x, next.x).getItpf().applySubstitution(TRSSubstitution.create(ImmutableCreator.create(combined), true)));
            current = next;
        }
        return ItpfAnd.create(ImmutableCreator.create(conj)).normalize();
    }

    @Override
    public List<? extends List<Node>> paths(Node node, int length, int position) {
        List<LinkedList<Node>> res = new ArrayList<LinkedList<Node>>();
        LinkedList<Node> first = new LinkedList<Node>();
        first.add(node);
        res.add(first);
        this.buildPrePost();
        for (int i = position-1; i>= 0; i--) {
            this.extendPathPre(res);
        }
        for (int i = length-position-2; i>= 0; i--) {
            this.extendPathPost(res);
        }
        return res;
    }

    protected void extendPathPre(List<LinkedList<Node>> paths) {
        int size = paths.size();
        for (int i = 0; i < size; i++) {
            LinkedList<Node> currentPath = paths.get(i);
            Node currentNode = currentPath.getFirst();
            Set<Node> predec = this.pre.get(currentNode).keySet();
            if (predec == null || predec.size() == 0) {
                paths.remove(i);
                i--;
                size --;
            } else {
                Iterator<Node> predecIter = predec.iterator();
                Node first = predecIter.next();
                while (predecIter.hasNext()) {
                    LinkedList<Node> path = new LinkedList<Node>(currentPath);
                    path.addFirst(predecIter.next());
                    paths.add(path);
                }
                currentPath.addFirst(first);
            }
        }
    }

    protected void extendPathPost(List<LinkedList<Node>> paths) {
        int size = paths.size();
        for (int i = 0; i < size; i++) {
            LinkedList<Node> currentPath = paths.get(i);

            Node currentNode = currentPath.getLast();
            Set<Node> succ = this.post.get(currentNode).keySet();
            if (succ == null || succ.size() == 0) {
                paths.remove(i);
                i--;
                size --;
            } else {
                Iterator<Node> succIter = succ.iterator();
                Node first = succIter.next();
                while (succIter.hasNext()) {
                    LinkedList<Node> path = new LinkedList<Node>(currentPath);
                    path.addLast(succIter.next());
                    paths.add(path);
                }
                currentPath.addLast(first);
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
                    Map<Node, Map<Node, IdpEdge>> preMap = new LinkedHashMap<Node, Map<Node, IdpEdge>>();
                    Map<Node, Map<Node, IdpEdge>> postMap = new LinkedHashMap<Node, Map<Node, IdpEdge>>();
                    for (Node n : this.nodes) {
                        preMap.put(n, new LinkedHashMap<Node, IdpEdge>());
                        postMap.put(n, new LinkedHashMap<Node, IdpEdge>());
                    }
                    for (IdpEdge edge : this.edges) {
                        preMap.get(edge.getTo()).put(edge.getFrom(), edge);
                        postMap.get(edge.getFrom()).put(edge.getTo(), edge);
                    }
                    Map<Node, ImmutableMap<Node, IdpEdge>> preImmu = new LinkedHashMap<Node, ImmutableMap<Node, IdpEdge>>();
                    Map<Node, ImmutableMap<Node, IdpEdge>> postImmu = new LinkedHashMap<Node, ImmutableMap<Node, IdpEdge>>();
                    for (Map.Entry<Node, Map<Node, IdpEdge>> entry : preMap.entrySet()) {
                        preImmu.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
                    }
                    for (Map.Entry<Node, Map<Node, IdpEdge>> entry : postMap.entrySet()) {
                        postImmu.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
                    }
                    this.pre = ImmutableCreator.create(preImmu);
                    this.post = ImmutableCreator.create(postImmu);
                }
            }
        }
    }

    // #############################################################################
    // SCCs
    // #############################################################################
    @Override
    public ImmutableList<ImmutableSet<Node>> getSCCs() {
        if (this.sccs == null) {
            synchronized(this) {
                if (this.sccs == null) {
                    if (this.isSCC == YNM.YES) {
                        List<ImmutableSet<Node>> tmp = new ArrayList<ImmutableSet<Node>>(1);
                        tmp.add(this.getNodes());
                        return this.sccs = ImmutableCreator.create(tmp);
                    } else {
                        this.buildPrePost();
                        // do tarjan
                        if (this.getNodes().size() == 0 || this.getEdges().size() == 0) {
                            return this.sccs = ImmutableCreator.create(Collections.<ImmutableSet<Node>>emptyList());
                        }

                        List<ImmutableSet<Node>> acc = new ArrayList<ImmutableSet<Node>>();
                        Set<Node> remainingStartNodes = new LinkedHashSet<Node>(this.getNodes());
                        Map<Node, Integer> indices = new LinkedHashMap<Node, Integer>();
                        Map<Node, Integer> lowLinks = new LinkedHashMap<Node, Integer>();
                        int index = 0;
                        while (remainingStartNodes.size() > 0) {
                            Stack<Node> S = new Stack<Node>();
                            Iterator<Node> i = remainingStartNodes.iterator();
                            Node startNode = i.next();
                            i.remove();
                            index = this.tarjan(startNode, index, S, indices, lowLinks, acc);
                            remainingStartNodes.removeAll(indices.keySet());
                        }
                        return this.sccs = ImmutableCreator.create(acc);
                    }
                }
            }
        }
        return this.sccs;
    }

    protected int tarjan (Node v, int index, Stack<Node> S, Map<Node, Integer> indices, Map<Node, Integer> lowLinks, List<ImmutableSet<Node>> sccs) {
        if (indices.containsKey(v)) {
            return index;
        }
        indices.put(v, index);
        lowLinks.put(v, index);
        int vIndex = index;
        Integer vLow = index;
        index ++;
        S.push(v);
        for (Node succ : this.post.get(v).keySet()) {
            Integer toIndex = indices.get(succ);
            if (toIndex == null) {
                index = this.tarjan(succ, index, S, indices, lowLinks, sccs);
                Integer toLow = lowLinks.get(succ);
                if (toLow < vLow) {
                    lowLinks.put(v, toLow);
                    vLow = toLow;
                }
            } else if (S.contains(succ)) {
                if (toIndex < vLow) {
                    lowLinks.put(v, toIndex);
                    vLow = toIndex;
                }
            }
        }
        if (vLow == vIndex) {
            Set<Node> scc = new LinkedHashSet<Node>();
            while (true) {
                Node w = S.pop();
                scc.add(w);
                if (v == w) {
                    break;
                }
            }
            boolean ok = scc.size() > 1;
            // check self loops
            if (!ok) {
                for (Node succ : this.post.get(v).keySet()) {
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
        return index;
    }

    // #############################################################################
    // DOT
    // #############################################################################
    @Override
    public String toDOT() {
        return this.toDOT(false);
    }

    /**
     * Returns a String containing a DOT representation of this
     * graph.
     * @param showNrs Indicates whether or not node numbers should
     *                be shown in the node labels.
     * @return A String containing a DOT representation of this
     *         graph.
     */
    public String toDOT(boolean showNrs) {

        StringBuffer t = new StringBuffer(
                "digraph idp_graph {\nnode [outthreshold=100, inthreshold=100];");
        this.buildPrePost();
        for (Map.Entry<Node, ImmutableMap<Node, IdpEdge>> entry: this.post.entrySet()) {
            Node from = entry.getKey();
            t.append( from.id + " [");
            t.append("label=\""
                    + (showNrs ? from.id + ": " : "")
                    + this.getDOTNodeLabelText(IDependencyGraph.DOT, from) + "\", ");
            t.append(this.getDOTFormatForNodeLabels(IDependencyGraph.DOT, from));
            t.append("];");

            if (entry.getValue().size() == 0)  {
                continue;
            }
            t.append(from.id + " -> {");
            for (Node succ : entry.getValue().keySet()) {
                t.append(succ.id + " ");
            }
            t.append("};\n");
        }
        return t.toString() + "}\n";
    }

    /**
     * Returns a formatting String for the DOT representation of
     * a node label in this graph dependent on the method called for
     * the representation, the node and a parameter object.
     * @param method An integer constant describing the calling
     *               method for DOT representation. Can be
     *               DOT, SAVE, EDGES, INTERACTIVE, DOTDOT1 or
     *               DOTDOT2.
     * @param node The node labeled with this format.
     * @return A formatting String for the DOT representation of
     *         a node label in this graph.
     */
    protected String getDOTFormatForNodeLabels(int method, Node node) {
        switch (method) {
            case DOT: case DOTDOT2:
                return "fontsize=16";
            case SAVE: case EDGES: case DOTDOT1:
                return "fontsize=16";
            case INTERACTIVE:
                return "fontsize=10";
        }
        return "";
    }

    /**
     * Returns the label text of a node in the DOT representation of
     * this graph dependent on the calling method for the DOT
     * representation and the node.
     * @param method An integer constant describing the calling
     *               method for DOT representation. Can be
     *               DOT, SAVE, EDGES or INTERACTIVE.
     * @param node The node to be labeled with the text.
     * @return The specified node's label text in the DOT
     *         representation.
     */
    protected String getDOTNodeLabelText(final int method, final Node node) {
        switch (method) {
            case DOT: case SAVE:
                return node.export(new Dotty_Util());
            case EDGES: case INTERACTIVE:
                return node.export(new Dotty_Util());
        }
        return "";
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String export(Export_Util o) {
        return this.export(o, null, VerbosityLevel.MIDDLE);
    }

    @Override
    public String export(Export_Util o, IDPPredefinedMap predefinedMap, VerbosityLevel verbosityLevel) {
        this.buildPrePost();
        final StringBuilder s = new StringBuilder();
        if (this.nodes.isEmpty()) {
        } else {
            // s.append(o.set(this.P, Export_Util.RULES));
            for (Node n : this.nodes) {
                s.append(n.export(o, predefinedMap, verbosityLevel));
                s.append(o.linebreak());
            }
            s.append(o.linebreak());
            for (IdpEdge edge : this.edges) {
                StringBuilder indent = new StringBuilder();
                indent.append("   (");
                indent.append(edge.getFrom().id);
                indent.append(") -> (");
                indent.append(edge.getTo().id);
                indent.append("), if ");
                indent.append(edge.getItpf().export(o, predefinedMap, verbosityLevel));
                s.append(o.indent(indent.toString()));
                s.append(o.linebreak());
            }
            s.append(o.cond_linebreak());
        }
        return s.toString();
    }
}