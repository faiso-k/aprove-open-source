package aprove.verification.complexity.CpxRntsProblem.Processors;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Algorithms.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.*;
import aprove.verification.complexity.CpxTypedWeightedTrsProblem.*;
import aprove.verification.complexity.CpxWeightedTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;


/**
 * This processor is applicable when the analysis has failed, i.e. when an INF
 * runtime bound was inferred. The processor applies narrowing to the original
 * TRS rules that correspond to the current SCC (where the INF bound occurred)
 * and then applies size abstraction to translate the narrowed TRS rules
 * to new RNTS rules that replace the current SCC.
 *
 * The processor uses the `retryCount` counter of the RNTS obligation:
 * The counter is increased by applying this processor and this processor
 * is only applicable if the `retryCount` counter is below a maximal number
 * of steps (see `MAX_STEPS`).
 *
 * ###########################
 * @warning TL;DR: use the InliningProcessor after the RetryProcessor!
 *
 * When using this processor, any pre-processing of the RNTS
 * (e.g. the InliningProcessor) has to be repeated! As the current SCC is
 * replaced by size-abstracted rules from the original TRS, the pre-processing
 * is not applied to these rules. This can lead to inconsistencies with
 * the analysis order (i.e. the todo list found by the AnalysisOrder processor),
 * as the pre-processing might simplify some SCCs (or even remove functions).
 * If this leads to more problems, one could also re-run the AnalysisOrder
 * processor (which is currently only applicable if the todo list does not
 * exist, but could be modified.
 * ###########################
 *
 * @author mnaaf
 *
 */
public class CpxRntsRetryProcessor extends ProcessorSkeleton {

    private static final int MAX_STEPS = 2;

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (obl instanceof CpxRntsProblem) && hasFailed((CpxRntsProblem)obl);
    }

    // returns true iff an INF runtime bound was inferred and the retry count is below MAX_STEPS
    private static boolean hasFailed(CpxRntsProblem rnts) {
        if (!rnts.hasTodo() || rnts.getRetryCount() >= MAX_STEPS) {
            return false;
        }
        for (FunctionSymbol fun : rnts.getTodo()) {
            if (rnts.hasResult(fun)) {
                ComplexitySummary cpx = rnts.getResult(fun);
                if (cpx.hasRuntime() && cpx.getRuntime().isInfinite()) {
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        CpxRntsProblem rnts = (CpxRntsProblem)obl;
        CpxTypedWeightedTrsProblem trs = rnts.getTrs();

        //drop rules from the current SCC and mark them as todo
        Set<FunctionSymbol> funs = rnts.getTodo();
        Set<RntsRule> newRules = rnts.getRules().stream()
                .filter(r -> !funs.contains(r.getRootSymbol()))
                .collect(Collectors.toSet());
        Set<WeightedRule> todo = trs.getRules().stream()
                .filter(r -> funs.contains(r.getRootSymbol()))
                .collect(Collectors.toSet());

        //always narrow at least once
        Set<WeightedRule> curr = todo;
        curr = TrsNarrowing.narrowRules(curr,trs.getRules(),trs.getDefinedSymbols());

        //if this did not help previously, do 2 narrow steps at once (possibly multiple times)
        for (int i=0; i < rnts.getRetryCount(); ++i) {
            curr = TrsNarrowing.narrowRules(curr,trs.getRules(),trs.getDefinedSymbols());
            curr = TrsNarrowing.narrowRules(curr,trs.getRules(),trs.getDefinedSymbols());
        }

        //initialize data for size abstraction
        LinkedHashSet<WeightedRule> newTrsRules = new LinkedHashSet<>();
        LinkedHashSet<RntsRule> newRntsRules = new LinkedHashSet<>();
        FreshNameGenerator fng = new FreshNameGenerator(CollectionUtils.getNames(rnts.getVariables()),FreshNameGenerator.VARIABLES);
        List<String> argNames = new ArrayList<String>();
        for (int i=0; i < rnts.getMaxArity(); ++i) {
            argNames.add(rnts.getArgumentName(i));
        }

        //apply size abstraction to convert the narrowed rules back to RNTS rules
        newTrsRules.addAll(curr);
        for (WeightedRule rule : curr) {
            RntsRule abstrRule = SizeAbstraction.abstractRule(
                    rule.getRule(),
                    SimplePolynomial.create(rule.getWeight()),
                    argNames,
                    fng,
                    trs);
            newRntsRules.add(abstrRule);
        }
        newRules.addAll(newRntsRules);
        rnts = rnts.cloneWithTodoRetry(funs); //this will increase retryCount
        rnts = rnts.cloneWithNewRules(ImmutableCreator.create(newRules));

        return ResultFactory.proved(rnts, BothBounds.create(), new RetryTechniqueProof(todo,newTrsRules,newRntsRules));

    }

    private static class RetryTechniqueProof extends CpxProof {
        private final Set<WeightedRule> oldRules, newRules;
        private final Set<RntsRule> newRntsRules;

        public RetryTechniqueProof(final Set<WeightedRule> old, final Set<WeightedRule> now, final Set<RntsRule> rnts) {
            this.oldRules = old;
            this.newRules = now;
            this.newRntsRules = rnts;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder s = new StringBuilder();
            s.append(o.escape("Performed narrowing of the following TRS rules:") + o.cond_linebreak());
            s.append(o.set(oldRules, Export_Util.RULES));
            s.append(o.cond_linebreak());

            s.append(o.escape("And obtained the following new TRS rules:") + o.cond_linebreak());
            s.append(o.set(newRules, Export_Util.RULES));
            s.append(o.cond_linebreak());

            s.append(o.escape("Which were then size abstracted to RNTS rules to simplify the current SCC:") + o.cond_linebreak());
            s.append(o.set(newRntsRules, Export_Util.RULES));
            s.append(o.cond_linebreak());
            return s.toString();
        }
    }

}
