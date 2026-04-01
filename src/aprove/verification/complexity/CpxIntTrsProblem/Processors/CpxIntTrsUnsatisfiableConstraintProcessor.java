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

public class CpxIntTrsUnsatisfiableConstraintProcessor extends CpxIntTrsProcessor {

    private static final Set<ConstraintInformation> maybeSatisfiable = new LinkedHashSet<>();

    public static class UnsatisfiableConstraintProof extends Proof.DefaultProof {

        private Set<CpxIntTupleRule> removed;

        public UnsatisfiableConstraintProof(Set<CpxIntTupleRule> removed) {
            this.removed = removed;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append(o
                .escape("The following rules have unsatisfiable constraints and can be removed from the problem:"));
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
        Set<CpxIntTupleRule> removed = new LinkedHashSet<>();

        for (CpxIntTupleRule rule : obl.getK().keySet()) {
            ConstraintInformation constraint = rule.getConstraintInformation();
            if (CpxIntTrsUnsatisfiableConstraintProcessor.maybeSatisfiable.contains(constraint)) {
                continue;
            }

            if (constraint.isUnsatisfiable(aborter)) {
                removed.add(rule);
            } else {
                CpxIntTrsUnsatisfiableConstraintProcessor.maybeSatisfiable.add(constraint);
            }
        }
        if (removed.isEmpty()) {
            return ResultFactory.unsuccessful();
        }

        return ResultFactory.proved(
            obl.createSubproblemByRemovingRulesCompletely(removed),
            BothBounds.create(),
            new UnsatisfiableConstraintProof(removed));
    }

    @Override
    boolean isCpxIntTrsApplicable(CpxIntTrsProblem obl) {
        return true;
    }
}
