package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Implication;
import aprove.verification.oldframework.Logic.Formulas.Visitors.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;

@NoParams
public class LiftingProcessor extends TheoremProverProcessor {

    @Override
    protected Result process(TheoremProverObligation obligationInput, BasicObligationNode obligationNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {

        if(obligationInput.getHypotheses().size() == 0) {
            return ResultFactory.notApplicable();
        }

        Formula formula = obligationInput.getFormula();

        if (formula.equals(FormulaTruthValue.FALSE)) {

            Set<Formula> premises = new LinkedHashSet<Formula>();

            for(Pair<Formula,Set<VariableSymbol>> hypothesis : obligationInput.getHypothesesAsSet()) {
                if(hypothesis.y.isEmpty()) {
                    premises.add(hypothesis.x.deepcopy());
                }
            }

            if(!premises.isEmpty()) {
                Formula newFormula = Implication.create(And.create(premises), formula.deepcopy());
                TheoremProverObligation newObligation = new TheoremProverObligation(newFormula, obligationInput);
                return ResultFactory.proved(newObligation, YNMImplication.EQUIVALENT, new LiftingProof(newObligation));
            }
            else{
                return ResultFactory.unsuccessful();
            }
        }

        for(Pair<Formula,Set<VariableSymbol>> hypothesis : obligationInput.getHypothesesAsSet()) {

            if(hypothesis.getValue().isEmpty()) {
                Formula evaluatedHypothesis = FormulaEvaluationVisitor.apply(hypothesis.x,obligationInput.getProgram());

                Formula newFormula = Implication.create(evaluatedHypothesis, obligationInput.getFormula().deepcopy());

                Triple<Formula,AlgebraVariable,AlgebraTerm> te = InverseSubstitutionProcessor.inverseSubstitution(newFormula, obligationInput.getAllVariables());

                if(te != null && !newFormula.equals(te.x)) {

                    TheoremProverObligation newObligation = new TheoremProverObligation(newFormula,obligationInput);
                    Map<HypothesisPair,Integer> hypotheses = obligationInput.getHypotheses();
                    hypotheses.remove(hypothesis);
                    newObligation.setHypotheses(hypotheses);

                    return ResultFactory.proved(newObligation, YNMImplication.EQUIVALENT, new LiftingProof(newObligation));

                }

            }

        }

        return ResultFactory.notApplicable();

    }

}
