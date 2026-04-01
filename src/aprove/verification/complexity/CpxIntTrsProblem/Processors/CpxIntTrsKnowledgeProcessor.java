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
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class CpxIntTrsKnowledgeProcessor extends CpxIntTrsProcessor {

    public static class KnowledgePropagationProof extends Proof.DefaultProof {

        private LinkedHashMap<CpxIntTupleRule, ComplexityValue> propagated;

        public KnowledgePropagationProof(LinkedHashMap<CpxIntTupleRule, ComplexityValue> propagated) {
            this.propagated = propagated;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append(o.escape("The known complexity of the following rules was deduced by knowledge propagation:"));
            sb.append(o.set(this.propagated.keySet(), Export_Util.RULES));
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
        LinkedHashMap<CpxIntTupleRule, ComplexityValue> k = new LinkedHashMap<>();
        k.putAll(obl.getK());
        LinkedHashMap<CpxIntTupleRule, ComplexityValue> propagated = new LinkedHashMap<>();

        boolean changed;
        do {
            changed = false;
            rule: for (CpxIntTupleRule rule : obl.getK().keySet()) {
                Set<CpxIntTupleRule> pre = graph.pre(rule);
                ComplexityValue complexity = ComplexityValue.constant();
                for (CpxIntTupleRule predecessor : pre) {
                    ComplexityValue predComplexity = k.get(predecessor);
                    if (predComplexity.isInfinite()) {
                        continue rule;
                    }
                    complexity = complexity.max(predComplexity);
                }
                ComplexityValue oldComplexity = k.get(rule);
                if (complexity.compareTo(oldComplexity) < 0) {
                    changed = true;
                    propagated.put(rule, complexity);
                    k.put(rule, complexity);
                    break rule;
                }
            }
        } while (changed);

        if (propagated.isEmpty()) {
            return ResultFactory.unsuccessful();
        }

        return ResultFactory.proved(
            obl.createSubproblem(obl.getDepGraph(aborter), ImmutableCreator.create(k)),
            BothBounds.create(),
            new KnowledgePropagationProof(propagated));
    }

    @Override
    boolean isCpxIntTrsApplicable(CpxIntTrsProblem obl) {
        return true;
    }

}
