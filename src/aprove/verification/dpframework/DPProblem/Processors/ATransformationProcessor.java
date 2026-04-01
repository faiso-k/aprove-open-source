package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class ATransformationProcessor extends QDPProblemProcessor {

    private final boolean keepMinimality;

    @ParamsViaArgumentObject
    public ATransformationProcessor(final Arguments arguments) {
        this.keepMinimality = arguments.keepMinimality;
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        if (Options.certifier.isCeta()) {
            return false;
        }
        // check against progress
        if (qdp.getMaxArity() == 0) {
            return false;
        }
        // check against applicative
        final QApplicativeUsableRules qaur = qdp.getApplicativeInfo();
        if (qaur == null) {
            return false;
        }

        final boolean innermost = qdp.QsupersetOfLhsR();

        if (!innermost) {
            // check new minimality
            // okay, we will loose minimality
            if (qdp.getMinimal() && this.keepMinimality) {
                return false;
            }
            // and we currently only handle Q = empty if not innermost
            if (!qdp.getQ().isEmpty()) {
                return false;
            }
        }

        return true;
    }


    @Override
    protected Result processQDPProblem(final QDPProblem qdp, final Abortion aborter) throws AbortionException {
        if (Globals.useAssertions) {
            assert(this.isApplicable(qdp));
        }

        final Pair<Map<Rule,Rule>,QTRSProblem> result = qdp.getATransformed();
        if (result == null) {
            return ResultFactory.notApplicable();
        }

        final boolean innermost = qdp.QsupersetOfLhsR();
        final boolean lostMinimal = qdp.getMinimal() && !innermost;
        final boolean newMinimal = qdp.getMinimal() && innermost;

        final Map<Rule,Rule> ruleMap = result.x;
        // now transform graph structure
        final Graph<Rule,?> newGraph = new Graph<Rule,QDPProblem>();
        final Graph<Rule,?> oldGraph = qdp.getDependencyGraph().getGraph();
        final Set<Node<Rule>> oldNodes = oldGraph.getNodes();
        final Map<Node<Rule>,Node<Rule>> nodeMap = new HashMap<Node<Rule>, Node<Rule>>(oldNodes.size());
        for (final Node<Rule> oldNode : oldNodes) {
            final Rule rule = ruleMap.get(oldNode.getObject());
            final Node<Rule> newNode = new Node<Rule>(rule);
            nodeMap.put(oldNode, newNode);
            newGraph.addNode(newNode);
        }
        for (final Edge<?,Rule> edge : oldGraph.getEdges()) {
            newGraph.addEdge(nodeMap.get(edge.getStartNode()), nodeMap.get(edge.getEndNode()));
        }
        final QDPProblem aqdp =  QDPProblem.create(newGraph, result.y, newMinimal);

        final Implication impl = YNMImplication.EQUIVALENT; // currently we are always complete

        final Result res = ResultFactory.proved(aqdp, impl, new ATransformationProof(lostMinimal, qdp, aqdp));
        return res;

    }

    private static class ATransformationProof extends QDPProof {

        private final boolean lostMinimal;
        private final QDPProblem origQDP;
        private final QDPProblem resultQDP;

        private ATransformationProof(final boolean lostMinimal,
                final QDPProblem origQDP,
                final QDPProblem resultQDP) {
            this.lostMinimal = lostMinimal;
            this.origQDP = origQDP;
            this.resultQDP = resultQDP;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            String res =
                "We have applied the A-Transformation "+o.cite(Citation.FROCOS05)+" to get from an applicative problem to a standard problem. ";
            if (this.lostMinimal) {
                res += "As not all Q-normal forms are R-normal forms we cannot keep minimality. ";
            }
            return o.export(res);
        }

    }

    public static class Arguments {
        public boolean beComplete = true; // currently not supported
        public boolean keepMinimality = true;;
    }


}
