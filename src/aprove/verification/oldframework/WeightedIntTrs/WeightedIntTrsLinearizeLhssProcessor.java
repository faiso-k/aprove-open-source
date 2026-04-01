package aprove.verification.oldframework.WeightedIntTrs;

import static aprove.verification.oldframework.IntTRS.PoloRedPair.ToolBox.*;
import static java.util.stream.Collectors.*;

import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

public class WeightedIntTrsLinearizeLhssProcessor extends Processor.ProcessorSkeleton {

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        return processInternal((AbstractWeightedIntTermSystem<?>) obl);
    }

    private <T extends AbstractWeightedIntRule<T>> Result processInternal(AbstractWeightedIntTermSystem<T> obl) {
        Map<T, T> newRules = obl.getRules().stream().collect(toMap(x -> x, this::linearizeLhss));
        if (obl.getRules().containsAll(newRules.values())) {
            return ResultFactory.unsuccessful();
        } else {
            return ResultFactory.proved(obl.copyWithNewRules(newRules.values()), BothBounds.forConcreteBounds(), new LinearizedLhssProof<>(newRules));
        }
    }

    private <T extends AbstractWeightedIntRule<T>> T linearizeLhss(T r) {
        FreshNameGenerator fng = new FreshNameGenerator(r.getUsedNames(), FreshNameGenerator.VARIABLES);
        ArrayList<TRSTerm> newArgs = new ArrayList<>();
        TRSFunctionApplication newCond = r.getCondition();
        List<TRSTerm> newOutputVariables = new ArrayList<>(r.getLeftOutputVariables());
        for (TRSTerm arg: r.getLeft().getArguments()) {
            assert arg.isVariable();
            if (newArgs.contains(arg)) {
                TRSVariable x = TRSTerm.createVariable(fng.getFreshName("x",  false));
                newArgs.add(x);
                newCond = buildAnd(newCond, buildEq(x, arg));
                if (r.getLeftOutputVariables().contains(arg)) {
                    // TODO: check if this is correct
                    newOutputVariables.add(x);
                }
            } else {
                newArgs.add(arg);
            }
        }
        TRSFunctionApplication newLhs = TRSTerm.createFunctionApplication(r.getRootSymbol(), newArgs);
        return r.copy(newLhs, r.getRight(), newCond, newOutputVariables);
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (!(obl instanceof AbstractWeightedIntTermSystem<?>)) {
            return false;
        }
        AbstractWeightedIntTermSystem<?> its = (AbstractWeightedIntTermSystem<?>) obl;
        return its.getRules().stream().allMatch(x -> x.getLeft().getArguments().stream().allMatch(TRSTerm::isVariable));
    }

    private static class LinearizedLhssProof<T extends AbstractWeightedIntRule<T>> extends DefaultProof {

        Map<T, T> map;

        public LinearizedLhssProof(Map<T, T> map) {
            this.map = map;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append("Linearized lhss.");
            for (Entry<T, T> e: map.entrySet()) {
                if (!e.getKey().equals(e.getValue())) {
                    sb.append(o.paragraph());
                    sb.append(e.getKey().export(o));
                    sb.append(o.linebreak());
                    sb.append("was transformed to");
                    sb.append(o.linebreak());
                    sb.append(e.getValue().export(o));
                }
            }
            return sb.toString();
        }

    }

}
