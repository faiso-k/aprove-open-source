package aprove.verification.oldframework.WeightedIntTrs;

import static java.util.stream.Collectors.*;

import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.JBCOptions.*;
import aprove.verification.oldframework.IRSwT.*;
import aprove.verification.oldframework.IRSwT.IRSwTFormatTransformer.*;
import aprove.verification.oldframework.Utility.*;

public class WeightedIntTrsRemoveUnsupportedOperatorsProcessor extends Processor.ProcessorSkeleton {

    public static class Arguments {

        public static StaticOption<Boolean> cliPropagateLowerBounds = new StaticOption<>();
        private InstanceOption<Boolean> propagateLowerBounds = new InstanceOption<>(false, cliPropagateLowerBounds);

        public boolean propagateLowerBounds() {
            return propagateLowerBounds.get();
        }

        public void setPropagateLowerBounds(boolean b) {
            propagateLowerBounds.set(b);
        }

    }

    private Arguments args;

    @ParamsViaArgumentObject
    public WeightedIntTrsRemoveUnsupportedOperatorsProcessor(Arguments args) {
        this.args = args;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        return processInternal((AbstractWeightedIntTermSystem<?>) obl);
    }

    private <T extends AbstractWeightedIntRule<T>> Result processInternal(AbstractWeightedIntTermSystem<T> obl) {
        Map<T, Set<T>> map = obl.getRules().stream().collect(toMap(x -> x, x -> removeDivMod(x)));
        Set<T> newRules = map.values().stream().flatMap(x -> x.stream()).collect(toSet());
        if (newRules.equals(obl.getRules())) {
            return ResultFactory.unsuccessful();
        } else {
            ComplexityImplication imp;
            if (args.propagateLowerBounds()) {
                imp = SoundUpperUnsoundLowerBound.forConcreteBounds();
            } else {
                imp = UpperBound.forConcreteBounds();
            }
            return ResultFactory.proved(obl.copyWithNewRules(newRules), imp, new RemoveUnsupportedOperatorsProof<>(map));
        }
    }

    private <T extends AbstractWeightedIntRule<T>> Set<T> removeDivMod(T rule) {
        //hack an IGenerelisedRule
        FunctionSymbol hackFS = FunctionSymbol.create("hack123", rule.getRight().size());
        TRSFunctionApplication hackRhs = TRSTerm.createFunctionApplication(hackFS, rule.getRight());
        IGeneralizedRule hack = IGeneralizedRule.create(rule.getLeft(), hackRhs, rule.getCondition(), rule.getLeftOutputVariables());

        Set<IGeneralizedRule> newRules = IRSwTFormatTransformer.removeDivModAndNotAndNotEqualAndOrAndFalse(hack, RoundingBehaviour.UNKNOWN, IDPPredefinedMap.DEFAULT_MAP, false, true);

        //undo hack
        Set<T> res = new LinkedHashSet<>();
        for (IGeneralizedRule newRule : newRules) {
            TRSFunctionApplication newRuleRhs = (TRSFunctionApplication) newRule.getRight();
            if (newRuleRhs.getRootSymbol().equals(hackFS)) {
                List<TRSFunctionApplication> newRhs = new ArrayList<>();
                for (TRSTerm t : newRuleRhs.getArguments()) {
                    newRhs.add((TRSFunctionApplication)t);
                }
                res.add(rule.copy(newRule.getLeft(), newRhs, (TRSFunctionApplication) newRule.getCondTerm(), newRule.getLeftOutputVariables()));
            } else {
                res.add(rule.copy(newRule.getLeft(), Collections.singletonList((TRSFunctionApplication)newRule.getRight()), (TRSFunctionApplication) newRule.getCondTerm(), SimplePolynomial.ZERO, SimplePolynomial.ZERO, newRule.getLeftOutputVariables()));
            }
        }
        return res;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof AbstractWeightedIntTermSystem<?>;
    }

    private static class RemoveUnsupportedOperatorsProof <T extends AbstractWeightedIntRule<T>> extends DefaultProof {

        Map<T, Set<T>> map;

        public RemoveUnsupportedOperatorsProof(Map<T, Set<T>> map) {
            super();
            this.map = map;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append("Removed unsupported operators like negation, div, and mod.");
            for (Entry<T, Set<T>> e: map.entrySet()) {
                if (!Collections.singleton(e.getKey()).equals(e.getValue())) {
                    sb.append(o.paragraph());
                    sb.append(e.getKey().export(o));
                    sb.append(o.linebreak());
                    sb.append("was transformed to");
                    for (T r: e.getValue()) {
                        sb.append(o.linebreak());
                        sb.append(r.export(o));
                    }
                }
            }
            return sb.toString();
        }

    }

}
