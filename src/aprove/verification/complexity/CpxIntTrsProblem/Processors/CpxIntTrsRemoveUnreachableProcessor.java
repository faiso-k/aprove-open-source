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

public class CpxIntTrsRemoveUnreachableProcessor extends CpxIntTrsProcessor {

    public static class RemoveUnreachableProof extends Proof.DefaultProof {

        private Set<CpxIntTupleRule> removed;

        public RemoveUnreachableProof(Set<CpxIntTupleRule> removed) {
            this.removed = removed;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb
                .append(o
                    .escape("The following cannot be reached from start rules and can be removed from the problem:"));
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

        Set<CpxIntTupleRule> reached = graph.getRulesReachableFrom(obl.getStartRules());

        Set<CpxIntTupleRule> removed = new LinkedHashSet<>();
        removed.addAll(obl.getK().keySet());
        removed.removeAll(reached);

        if (removed.isEmpty()) {
            return ResultFactory.unsuccessful();
        }

        return ResultFactory.proved(
            obl.createSubproblemByRemovingRulesCompletely(removed),
            BothBounds.create(),
            new RemoveUnreachableProof(removed));
    }

    @Override
    boolean isCpxIntTrsApplicable(CpxIntTrsProblem obl) {
        return true;
    }
}
