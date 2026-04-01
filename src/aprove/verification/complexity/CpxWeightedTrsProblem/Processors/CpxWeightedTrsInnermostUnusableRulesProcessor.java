package aprove.verification.complexity.CpxWeightedTrsProblem.Processors;

import java.util.LinkedHashSet;
import java.util.Optional;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxWeightedTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Simple processor that removes rules with non-basic lhs like
 *
 * f(f(...)) -> ...
 *
 * if there is a rule of the form
 *
 * f(X,Y,...) -> ...
 *
 * i.e. a rule where f is applied to variables only. Then this rule always has
 * to be used in innermost evaluation and the f(f(...)) rule can never be applied.
 *
 * @author mnaaf
 */
public class CpxWeightedTrsInnermostUnusableRulesProcessor extends CpxWeightedTrsProcessor {

    @Override
    protected boolean isCpxWeightedTrsApplicable(CpxWeightedTrsProblem obl) {
        return obl.isInnermost();
    }

    @Override
    protected Result processCpxWeightedTrs(CpxWeightedTrsProblem cpxTrs, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        CpxWeightedTrsInnermostUnusableRulesWorker worker = new CpxWeightedTrsInnermostUnusableRulesWorker();
        Result res = worker.processCpxWeightedTrs(cpxTrs, aborter);
        return res;
    }

    /**
     * Helper class to encapsulate the instance-dependent state of the
     * computation by the processor.
     */
    private static class CpxWeightedTrsInnermostUnusableRulesWorker {

        private CpxWeightedTrsProblem trs = null;

        private Optional<WeightedRule> getAllVariableRule(FunctionSymbol fun) {
            rule: for (WeightedRule r : trs.getRulesFor(fun)) {
                TRSFunctionApplication lhs = r.getLeft();
                if (!lhs.isLinear()) continue;
                for (TRSTerm arg : lhs.getArguments()) {
                    if (!arg.isVariable()) continue rule;
                }
                return Optional.of(r);
            }
            return Optional.empty();
        }

        private Set<FunctionSymbol> getInnerDefinedFuns(TRSFunctionApplication lhs) {
            Set<FunctionSymbol> res = lhs.getNonRootFunctionSymbols();
            res.retainAll(trs.getDefinedSymbols());
            return res;
        }

        //if r is not usable, returns a rule that has to be used instead.
        private Optional<WeightedRule> isUsableInnermost(Rule r) {
            Set<FunctionSymbol> inner = getInnerDefinedFuns(r.getLeft());
            for (FunctionSymbol fun : inner) {
                Optional<WeightedRule> witness = getAllVariableRule(fun);
                if (witness.isPresent()) {
                    return witness;
                }
            }
            return Optional.empty();
        }

        //deleted, witnesses are used as output parameter
        private Set<WeightedRule> processRules(Set<WeightedRule> rules, Set<WeightedRule> deleted, Set<WeightedRule> witnesses) {
            Set<WeightedRule> res = new LinkedHashSet<>();
            for (WeightedRule rule : rules) {
                Optional<WeightedRule> witness = isUsableInnermost(rule.getRule());
                if (witness.isPresent()) {
                    deleted.add(rule);
                    witnesses.add(witness.get());
                } else {
                    res.add(rule); //rule might be usable
                }
            }
            return res;
        }

        protected Result processCpxWeightedTrs(CpxWeightedTrsProblem cpxTrs, Abortion aborter) throws AbortionException {
            this.trs = cpxTrs;

            Set<WeightedRule> deleted = new LinkedHashSet<>();
            Set<WeightedRule> witness = new LinkedHashSet<>();
            Set<WeightedRule> newR = processRules(trs.getRules(),deleted,witness);

            if (deleted.isEmpty()) {
                return ResultFactory.unsuccessful();
            }

            CpxWeightedTrsProblem res = CpxWeightedTrsProblem.create(ImmutableCreator.create(newR), trs.isInnermost());
            return ResultFactory.proved(res, BothBounds.create(), new InnermostUnusableRulesProof(deleted,witness));
        }
    }

    private static class InnermostUnusableRulesProof extends CpxProof {
        private final Set<WeightedRule> deletedRules;
        private final Set<WeightedRule> witnessRules;

        public InnermostUnusableRulesProof(Set<WeightedRule> r, Set<WeightedRule> w) {
            deletedRules = r;
            witnessRules = w;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder s = new StringBuilder();
            s.append(o.escape("Removed the following rules with non-basic left-hand side, "));
            s.append(o.escape("as they cannot be used in innermost rewriting:"));
            s.append(o.cond_linebreak());
            s.append(o.set(deletedRules, Export_Util.RULES));
            s.append(o.cond_linebreak());

            s.append(o.escape("Due to the following rules that have to be used instead:"));
            s.append(o.cond_linebreak());
            s.append(o.set(witnessRules, Export_Util.RULES));
            s.append(o.cond_linebreak());

            return s.toString();
        }
    }

}
