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

public class WeightedIntTrsMoveArithmeticFromLhssToConstraintsProcessor extends Processor.ProcessorSkeleton {

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        return processInternal((AbstractWeightedIntTermSystem<?>) obl);
    }

    private <T extends AbstractWeightedIntRule<T>> Result processInternal(AbstractWeightedIntTermSystem<T> obl) throws AbortionException {
        Map<T, T> newRules = obl.getRules().stream().collect(toMap(x -> x, this::moveArithmeticToConstraint));
        if (obl.getRules().containsAll(newRules.values())) {
            return ResultFactory.unsuccessful();
        } else {
            return ResultFactory.proved(obl.copyWithNewRules(newRules.values()), BothBounds.forConcreteBounds(), new MovedArithmeticToConstraintsProof<>(newRules));
        }
    }

    private <T extends AbstractWeightedIntRule<T>> T moveArithmeticToConstraint(T rule) {
        FreshNameGenerator fng = new FreshNameGenerator(rule.getUsedNames(), FreshNameGenerator.VARIABLES);
        ArrayList<TRSTerm> newArgs = new ArrayList<>();
        TRSFunctionApplication newCond = rule.getCondition();
        for (TRSTerm arg: rule.getLeft().getArguments()) {
            if (arg.isVariable()) {
                newArgs.add(arg);
            } else {
                TRSVariable x = TRSTerm.createVariable(fng.getFreshName("x", false));
                newArgs.add(x);
                newCond = buildAnd(newCond, buildEq(x, arg));
            }
        }
        TRSFunctionApplication newLhs = TRSTerm.createFunctionApplication(rule.getRootSymbol(), newArgs);
        return rule.copy(newLhs, rule.getRight(), newCond, rule.getLeftOutputVariables());
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof AbstractWeightedIntTermSystem<?>;
    }

    private static class MovedArithmeticToConstraintsProof <T extends AbstractWeightedIntRule<T>> extends DefaultProof {

        Map<T, T> map;

        public MovedArithmeticToConstraintsProof(Map<T, T> map) {
            super();
            this.map = map;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append("Moved arithmethic from lhss to constraints.");
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
