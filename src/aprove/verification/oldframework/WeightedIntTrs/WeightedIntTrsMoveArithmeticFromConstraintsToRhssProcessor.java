package aprove.verification.oldframework.WeightedIntTrs;

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
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.oldframework.Utility.*;

public class WeightedIntTrsMoveArithmeticFromConstraintsToRhssProcessor extends Processor.ProcessorSkeleton {

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        return processInternal((AbstractWeightedIntTermSystem<?>) obl);
    }

    private <T extends AbstractWeightedIntRule<T>> Result processInternal(AbstractWeightedIntTermSystem<T> obl) {
        Map<T, T> newRules = obl.getRules().stream().collect(toMap(x -> x, this::moveArithmeticToRhss));
        if (obl.getRules().containsAll(newRules.values())) {
            return ResultFactory.unsuccessful();
        } else {
            return ResultFactory.proved(obl.copyWithNewRules(newRules.values()), BothBounds.forConcreteBounds(), new MovedArithmeticFromConstraintsProof<>(newRules));
        }
    }

    private <T extends AbstractWeightedIntRule<T>> T moveArithmeticToRhss(T rule) {
        Stack<TRSFunctionApplication> todo = new Stack<>();
        todo.push(rule.getCondition());
        List<TRSFunctionApplication> newRhs = new ArrayList<>(rule.getRight());
        while (!todo.isEmpty()) {
            TRSFunctionApplication current = todo.pop();
            if (current.getRootSymbol().equals(Func.Land.asFunctionSymbol())) {
                for (TRSTerm t: current.getArguments()) {
                    todo.push((TRSFunctionApplication) t);
                }
            } else if (current.getRootSymbol().equals(Func.Eq.asFunctionSymbol())) {
                if (current.getArgument(0).isVariable()) {
                    newRhs.replaceAll(fA -> fA.applySubstitution(TRSSubstitution.create((TRSVariable) current.getArgument(0), current.getArgument(1))));
                } else if (current.getArgument(1).isVariable()) {
                    newRhs.replaceAll(fA -> fA.applySubstitution(TRSSubstitution.create((TRSVariable) current.getArgument(1), current.getArgument(0))));
                }
            }
        }
        return rule.copy(rule.getLeft(), newRhs, rule.getLeftOutputVariables());
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof AbstractWeightedIntTermSystem<?>;
    }

    private static class MovedArithmeticFromConstraintsProof <T extends AbstractWeightedIntRule<T>> extends DefaultProof {

        Map<T, T> map;

        public MovedArithmeticFromConstraintsProof(Map<T, T> map) {
            this.map = map;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append("Moved arithmethic from constraints to rhss.");
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
