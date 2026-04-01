package aprove.verification.complexity.AcdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.AcdtProblem.*;
import aprove.verification.complexity.AcdtProblem.Utils.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Split each node of the Cdt graph which is not part of an SCC, i.e.
 * for each argument of the compound symbol introduce a new node with
 * the lhs and an unary compound symbol (and the argument).
 * replace it by new nodes which the same LHS end exactly
 * remove all tuple-subterms of the
 * RHS which do not have an outgoing edge (i.e. none of the edges
 * of the node "belongs" to the tuple-subterm).
 *
 * Use after CdtRemoveTrailingNodes processor - this will prevent generating
 * trivial Components.
 */
public class AcdtGraphSplitProcessor extends AcdtProblemProcessor{

    @Override
    protected boolean isCdtApplicable(AcdtProblem obl) {
        return true;
    }

    @Override
    protected Result processCdt(AcdtProblem cdtProblem, Abortion aborter)
            throws AbortionException {
        Set<BasicAcdtGraph> components = cdtProblem.getGraph().getComponents();
        List<AcdtProblem> todos = new ArrayList<AcdtProblem>(components.size());
        for (BasicAcdtGraph g : components) {
            todos.add(cdtProblem.createSubproblem(g));
        }

        if (todos.size() > 1) {
            return ResultFactory.provedMax(todos, BothBounds.create(), new CdtGraphSplitProof(todos.size()));
        } else {
            return ResultFactory.unsuccessful("Graph has only one component");
        }
    }

    private static class CdtGraphSplitProof extends DefaultProof {

        private final int numComponents;

        public CdtGraphSplitProof(int numComponents) {
            this.numComponents = numComponents;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("Split Graph in " + this.numComponents + " components.");
        }

    }
}
