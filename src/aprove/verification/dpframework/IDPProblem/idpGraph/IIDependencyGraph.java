/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.idpGraph;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.cap.*;
import aprove.verification.dpframework.IDPProblem.Processors.processorHistory.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Logic.*;
import immutables.*;

public interface IIDependencyGraph extends DOT_Able, Exportable, IDPExportable {

    public ImmutableSet<Node> getNodes();
    public ImmutableSet<IdpEdge> getEdges();
    public RuleAnalysis<GeneralizedRule> getNodeAnalysis();
    public IdpProcessorHistory getProcHistory();
    public YNM isSCC();
    public IdpEdge getEdge(Node from, Node to);
    public int getInDegree(Node node);
    public int getOutDegree(Node node);
    public IIDependencyGraph collapseNode(IDPRuleAnalysis ruleAnalysis, Node node, IDPProcessor proc);
    public IIDependencyGraph collapseNodes(IDPRuleAnalysis ruleAnalysis, Collection<Node> nodes, IDPProcessor proc);
    public IIDependencyGraph collapseNode(IDPRuleAnalysis ruleAnalysis, Node node, IECap cap, IDPProcessor proc);
    public IIDependencyGraph collapseNodes(IDPRuleAnalysis ruleAnalysis, Collection<Node> nodes, IECap cap, IDPProcessor proc);

    public ImmutableMap<Node, IdpEdge> getSuccessors(Node node);
    public ImmutableMap<Node, IdpEdge> getPredecessors(Node node);

    public Itpf itpfPath(VariableRenamedPath path);
    public List<? extends List<Node>> paths(Node node, int length, int position);

    public IIDependencyGraph changeLabels(Map<IdpEdge, Itpf> newFormulas, IDPProcessor proc);
    public IIDependencyGraph removeNodes(Set<Node> remove, YNM isSCC, IDPProcessor proc);
    public IIDependencyGraph restrictToNodes(Set<Node> newNodes, YNM isSCC, IDPProcessor proc);
    public IIDependencyGraph restrictToNodes(RuleAnalysis<GeneralizedRule> ruleAnalysis, Set<Node> newNodes, YNM isSCC, IDPProcessor proc);
    public IIDependencyGraph restrictToSccs(IDPProcessor proc);
    public ImmutableList<IIDependencyGraph> splitIntoSCCs(IDPProcessor proc);
    // public IIDependencyGraph renameNodes(Map<Node, Node> nodeRenaming, IDPProcessor proc);

    public boolean containsEdge(Node preNode, Node pfrule);
    public ImmutableList<ImmutableSet<Node>> getSCCs();



}