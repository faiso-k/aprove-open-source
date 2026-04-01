/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

@NoParams
public class IDPNodeCollapseProcessor extends IDPProcessor {

    private int maxInDegree = 10;
    private int maxOutDegree = 10;

    @Override
    public boolean isIDPApplicable(IDPProblem idp) {
        return true;
    }

    @Override
    protected Result processIDPProblem(IDPProblem idp, Abortion aborter)
            throws AbortionException {
        IIDependencyGraph graph = idp.getIdpGraph();
        ImmutableSet<Node> nodes = graph.getNodes();
        Node collapseNode = null;
        int minInOut = Integer.MAX_VALUE;
        for (Node node : nodes) {
            int out =  graph.getOutDegree(node);
            int in = graph.getInDegree(node);
            if (graph.getEdge(node, node) == null && out <= this.maxOutDegree && in <= this.maxInDegree) {
                if (out * in < minInOut) {
                    minInOut = out * in;
                    collapseNode = node;
                }
            }
        }
        if (collapseNode != null) {
            Set<GeneralizedRule> newP = new LinkedHashSet<GeneralizedRule>(idp.getP());
            newP.remove(collapseNode.rule);
            RuleAnalysis<GeneralizedRule> newPRules = new RuleAnalysis<GeneralizedRule>(ImmutableCreator.create(newP), idp.getRuleAnalysis().getPreDefinedMap());
            IDPRuleAnalysis newAnalysis = idp.getRuleAnalysis().change(null, newPRules, null);
            IIDependencyGraph newGraph = graph.collapseNode(newAnalysis, collapseNode, this);
            return ResultFactory.proved(idp.change(newGraph, null, null, null, this), YNMImplication.EQUIVALENT, new IDPNodeCollapseProve(collapseNode, newGraph));
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    private static class IDPNodeCollapseProve extends Proof.DefaultProof implements DOT_Able {

        private final Node collapsed;
        private final IIDependencyGraph newGraph;

        public IDPNodeCollapseProve(Node collapsed, IIDependencyGraph newGraph) {
            this.collapsed = collapsed;
            this.newGraph = newGraph;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder s = new StringBuilder();
            s.append("Collapsed node ");
            s.append("(");
            s.append(this.collapsed.id);
            s.append(").");
            return s.toString();
        }

        @Override
        public String toDOT() {
            return this.newGraph.toDOT();
        }
    }
}