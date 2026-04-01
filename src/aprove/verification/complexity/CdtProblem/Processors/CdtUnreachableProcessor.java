package aprove.verification.complexity.CdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CdtProblem.Utils.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Removes nodes not reachable from any basic term
 */
public class CdtUnreachableProcessor extends CdtProblemProcessor {

    @Override
    protected boolean isCdtApplicable(CdtProblem obl) {
        return !Options.certifier.isCpf();
    }

    @Override
    protected Result processCdt(CdtProblem cdtProblem, Abortion aborter)
            throws AbortionException {
        Graph<Cdt, BitSet> graph = cdtProblem.getGraph().getGraph();
        ArrayDeque<Node<Cdt>> todo =
            new ArrayDeque<Node<Cdt>>();
        for (Node<Cdt> node : graph.getNodes()) {
            if (this.lhsOk(node, cdtProblem)) {
                todo.add(node);
            }
        }

        Set<Node<Cdt>> reachables = graph.determineReachableNodes(todo);
        if (reachables.size() == graph.getNodes().size()) {
            return ResultFactory.unsuccessful("All nodes reachable");
        } else {
            Set<Cdt> unreachableCdts = new LinkedHashSet<Cdt>(cdtProblem.getTuples());
            for (Node<Cdt> reachableNode : reachables) {
                unreachableCdts.remove(reachableNode.getObject());
            }
            BasicCdtGraph newGraph =
                cdtProblem.getGraph().getSubgraph(reachables);
            CdtProblem newProblem = cdtProblem.createSubproblem(newGraph);
            return ResultFactory.proved(
                    newProblem, BothBounds.create(),
                    new CdtUnreachableProof(unreachableCdts));
        }
    }

    private boolean lhsOk(Node<Cdt> node, CdtProblem cdtProblem) {
        Set<FunctionSymbol> lhsFs = node.getObject().getRuleLHS().getFunctionSymbols();
        return Collections.disjoint(lhsFs, cdtProblem.getDefinedRSymbols());
    }

    public class CdtUnreachableProof extends CpxProof {

        private final Collection<Cdt> removed;

        public CdtUnreachableProof(Collection<Cdt> removed) {
           this.removed = removed;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append(o.escape("The following tuples could be removed as they are not reachable from basic start terms:"));
            sb.append(o.set(this.removed, Export_Util.RULES));
            return sb.toString();
        }

    }

}
