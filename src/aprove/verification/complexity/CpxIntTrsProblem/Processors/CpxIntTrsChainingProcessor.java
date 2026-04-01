package aprove.verification.complexity.CpxIntTrsProblem.Processors;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

public class CpxIntTrsChainingProcessor extends CpxIntTrsProcessor {

    public static class Arguments {
        public int maximalFanOut = 1;
        public boolean allowHarmful = false;
    }

    private final Arguments args;

    @ParamsViaArgumentObject
    public CpxIntTrsChainingProcessor(Arguments args) {
        this.args = args;
    }

    public static class ChainingProof extends Proof.DefaultProof {

        private final CpxIntTupleRule rule;
        private final Set<CpxIntTupleRule> replacingRules;
        private final Set<CpxIntTupleRule> chainedRules;

        public ChainingProof(
            CpxIntTupleRule rule,
            Set<CpxIntTupleRule> replacingRules,
            Set<CpxIntTupleRule> chainedRules)
        {
            this.rule = rule;
            this.replacingRules = replacingRules;
            this.chainedRules = chainedRules;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append(o.escape("The rule "));
            sb.append(this.rule.export(o));
            sb.append(o.escape(" was chained with") + o.cond_linebreak());
            sb.append(o.set(this.chainedRules, Export_Util.RULES));
            sb.append(o.escape("resulting in the following rules (replacing the original)") + o.cond_linebreak());
            sb.append(o.set(this.replacingRules, Export_Util.RULES));
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

        Map<CpxIntTupleRule, Set<CpxIntTupleRule>> outEdges = graph.getNodesWithOutEdges();

        nextRule: for (Entry<CpxIntTupleRule, Set<CpxIntTupleRule>> candidate : outEdges.entrySet()) {
            CpxIntTupleRule rule = candidate.getKey();
            Set<CpxIntTupleRule> chainedRules = candidate.getValue();
            if (chainedRules.size() > this.args.maximalFanOut) {
                continue;
            }
            if (!this.args.allowHarmful) {
                if (chainedRules.contains(rule)) {
                    // solving self loops is harmful
                    continue nextRule;
                }
                for (CpxIntTupleRule nextRule : chainedRules) {
                    // don't join with rules that are self looping
                    if (outEdges.get(nextRule).contains(nextRule)) {
                        continue nextRule;
                    }
                }
            }
            if (rule.getRights().size() != 1) {
                // currently we only handle Com_1, other cases would be more complicated
                continue;
            }

            Set<CpxIntTupleRule> replacingRules = new LinkedHashSet<>();

            for (CpxIntTupleRule next : chainedRules) {
                replacingRules.add(rule.chainWithRule(next, 0));
            }

            Map<CpxIntTupleRule, Set<CpxIntTupleRule>> replacements = new LinkedHashMap<>();
            replacements.put(rule, replacingRules);

            return ResultFactory.proved(obl.replaceRules(replacements), BothBounds.create(), new ChainingProof(
                rule,
                replacingRules,
                chainedRules));
        }
        return ResultFactory.unsuccessful();
    }

    @Override
    boolean isCpxIntTrsApplicable(CpxIntTrsProblem obl) {
        return true;
    }

}
