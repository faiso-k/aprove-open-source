package aprove.verification.complexity.CdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CdtProblem.Utils.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Implements the SccSplitP processor from Lars Noschinskis diploma thesis.
 */
public class CdtSccSplitProcessor extends CdtProblemProcessor{

    @Override
    protected boolean isCdtApplicable(CdtProblem obl) {
        return true;
    }

    @Override
    protected Result processCdt(CdtProblem cdtProblem, Abortion aborter)
            throws AbortionException {
        Map<Cycle<Cdt>, BasicCdtGraph> rcSccs =
            cdtProblem.getGraph().getReachingClosedSccs();
        List<CdtProblem> todos = new ArrayList<CdtProblem>(rcSccs.size());
        for (Map.Entry<Cycle<Cdt>,BasicCdtGraph> e : rcSccs.entrySet()) {
            BasicCdtGraph newGraph = e.getValue();
            Set<Cdt> keyObjects = e.getKey().getNodeObjects();
            Set<Cdt> newS = new LinkedHashSet<Cdt>(keyObjects);
            newS.retainAll(cdtProblem.getS());

            ImmutableSet<Cdt> newCdts = newGraph.getTuples();
            Set<Cdt> newK = new LinkedHashSet<Cdt>(newCdts);
            newK.removeAll(keyObjects);
            newK.retainAll(cdtProblem.getS());
            newK.addAll(cdtProblem.getK());
            newK.retainAll(newCdts);

            if (!newS.isEmpty()) {
                todos.add(cdtProblem.createSubproblem(
                        newGraph, ImmutableCreator.create(newS),
                        ImmutableCreator.create(newK)));
            }
        }
        if (todos.size() == 1) {
            CdtProblem todo = todos.get(0);
            if (todo.getTuples().equals(cdtProblem.getTuples())
                    && todo.getS().equals(cdtProblem.getS())) {
                return ResultFactory.unsuccessful("Graph has only one component");
            }
        }
        return ResultFactory.provedMax(todos, UpperBound.create(), new CdtSccSplitProof(todos.size()));
    }

    private static class CdtSccSplitProof extends CpxProof {

        private final int numComponents;

        public CdtSccSplitProof(int numComponents) {
            this.numComponents = numComponents;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("Split problem in " + this.numComponents + " new components.");
        }

    }
}
