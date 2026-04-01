package aprove.verification.complexity.CpxIntTrsProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

public class CpxIntTrsLeafRemovalProcessor extends CpxIntTrsProcessor {

    public static class LeafRemovalProof extends Proof.DefaultProof {

        private Set<CpxIntTupleRule> removed;

        public LeafRemovalProof(Set<CpxIntTupleRule> removed) {
            this.removed = removed;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append(o.escape("The following rules are leaves and can be removed from the problem:"));
            sb.append(o.set(this.removed, Export_Util.RULES));
            return sb.toString();
        }
    }

    @Override
    public Result processCpxIntTrs(
        CpxIntTrsProblem obl,
        BasicObligationNode oblNode,
        Abortion aborter,
        RuntimeInformation rti) throws AbortionException
    {
        CpxIntGraph graph = obl.getDepGraph(aborter);

        // TODO this does not correspond at all to LeafRemoval in the paper...
        Set<CpxIntTupleRule> reached = graph.getRulesReaching(obl.getUnknownTuples());

        Set<CpxIntTupleRule> removed = new LinkedHashSet<>();
        removed.addAll(obl.getK().keySet());
        removed.removeAll(reached);

        if (removed.isEmpty()) {
            return ResultFactory.unsuccessful();
        }

        return ResultFactory.proved(
            obl.createSubproblemByRemovingRulesCompletely(removed),
            BothBounds.create(),
            new LeafRemovalProof(removed));
    }

    @Override
    boolean isCpxIntTrsApplicable(CpxIntTrsProblem obl) {
        return true;
    }

}
