package aprove.verification.complexity.CpxTrsProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.AcdtProblem.Utils.*;
import aprove.verification.complexity.CdpProblem.Processors.Util.QtrsDirectGcdp.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Simplifies a CpxTrs by removing all rules not reachable from
 * basic terms.
 */
public class CpxTrsStarttermProcessor extends RuntimeComplexityTrsProcessor {

    @Override
    public boolean isRuntimeComplexityTrsApplicable(RuntimeComplexityTrsProblem obl) {
        return true;
    }

    @Override
    protected Result processRuntimeComplexityTrs(RuntimeComplexityTrsProblem cpx, Abortion aborter) throws AbortionException {
        Set<FunctionSymbol> definedSymbols = cpx.getDefinedSymbols();

        /* Compute the set of all rules possibly applicable to basic terms */
        Set<Rule> startRules = new LinkedHashSet<Rule>();
        for (Rule r : cpx.getR()) {
            Set<FunctionSymbol> argSyms =
                CollectionUtils.getFunctionSymbols(r.getLeft().getArguments());
            if (java.util.Collections.disjoint(definedSymbols, argSyms)) {
                startRules.add(r);
            }
        }

        /* Compute an overapproximation of the rules reachable from startRules */
        ImmutableRuleSet<Rule> renRules =
            new ImmutableRuleSet<Rule>(IcapAlgorithm.renumberedRules(cpx.getR()));
        IcapAlgorithm icap = IcapAlgorithm.create(renRules);
        UsableRulesCalculator urCalc = UsableRulesCalculator.create(renRules, icap);
        Set<Rule> relevantRules = new LinkedHashSet<Rule>();
        for (Rule startRule : startRules) {
            relevantRules.addAll(urCalc.estimateUsableRules(startRule));
        }
        relevantRules.addAll(startRules);

        if (relevantRules.equals(cpx.getR())) {
            return ResultFactory.unsuccessful("Could not remove any rule");
        } else {
            Set<Rule> removedRules = new LinkedHashSet<Rule>(cpx.getR());
            removedRules.removeAll(relevantRules);

            RuntimeComplexityTrsProblem newCpx = RuntimeComplexityTrsProblem.createSub(cpx, relevantRules);
            return ResultFactory.proved(
                    newCpx, BothBounds.create(),
                    new CpxTrsStarttermProof(removedRules));
        }
    }

    public class CpxTrsStarttermProof extends CpxProof {

        private final Collection<Rule> removedRules;

        public CpxTrsStarttermProof(Collection<Rule> removedRules) {
            this.removedRules = removedRules;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
           StringBuilder sb = new StringBuilder();
            sb.append(o.escape(
                    "The following rules are not relevant for behaviour " +
                    "on basic terms and have been removed:"));
            sb.append(o.set(this.removedRules, Export_Util.RULES));
            return sb.toString();
        }

    }

}
