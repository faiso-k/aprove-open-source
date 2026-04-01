package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Visitors.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;

/**
 * @author dickmeis
 * @version $Id$
 */
@NoParams
public class SymbolicOutermostEvaluationUnderHypothesisProcessor extends
        TheoremProverProcessor {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof TheoremProverObligation) {
            // even for indirect proofs
            // the hypotheses get removed before we can do an indirect proof
            return true;
        }
        return false;
    }

    @Override
    protected Result process(TheoremProverObligation obligationInput,
            BasicObligationNode obligationNode, Abortion aborter,
            RuntimeInformation rti) throws AbortionException {

        // check if hypothesis set is not empty
        Set<HypothesisPair> hypothesesSet = obligationInput
                .getAllUsedHypotheses(3);
        Set<Pair<Formula, Set<VariableSymbol>>> store = new LinkedHashSet<Pair<Formula, Set<VariableSymbol>>>(
                hypothesesSet);

        // evaluate formula with normal symbolic evaluation
        Formula newFormula;

        newFormula = this.evaluate(obligationInput.getProgram(),
                obligationInput.getFormula(), hypothesesSet);

        if (newFormula.equals(obligationInput.getFormula())) {
            return ResultFactory.unsuccessful();
        }

        boolean hypothesisUsed = !hypothesesSet.equals(store);
        Set<HypothesisPair> usedHypotheses = new LinkedHashSet<HypothesisPair>(
                obligationInput.getHypothesesAsSet());
        usedHypotheses.removeAll(hypothesesSet);

        // check if formula could be evaluated to a truth value
        if (newFormula instanceof FormulaTruthValue) {

            if (newFormula.equals(FormulaTruthValue.TRUE)) {
                if(!hypothesisUsed){
                    return ResultFactory.proved(
                            new SymbolicOutermostEvaluationProof(
                                new TheoremProverObligation(
                                    FormulaTruthValue.TRUE,
                                    obligationInput)));
                }
                else{
                    return ResultFactory.proved(
                            new SymbolicOutermostEvaluationUnderHypothesisProof(
                                new TheoremProverObligation(
                                    FormulaTruthValue.TRUE,
                                    obligationInput),
                                usedHypotheses));
                }
            }
            else {
                TheoremProverObligation newObligation = new TheoremProverObligation(
                        FormulaTruthValue.FALSE, obligationInput);

                if (obligationInput.getHypotheses().isEmpty()) {
                    if (!hypothesisUsed){
                        return ResultFactory.disproved(
                                new SymbolicOutermostEvaluationProof(
                                        newObligation));
                    }
                    else{
                        return ResultFactory.disproved(
                                new SymbolicOutermostEvaluationUnderHypothesisProof(
                                        newObligation,
                                        usedHypotheses));
                    }
                }
                else {
                    if (!hypothesisUsed){
                        return ResultFactory.proved(
                                newObligation,
                                YNMImplication.EQUIVALENT,
                                new SymbolicOutermostEvaluationProof(
                                        newObligation));
                    }
                    else{
                        return ResultFactory.proved(
                                newObligation,
                                YNMImplication.EQUIVALENT,
                                new SymbolicOutermostEvaluationUnderHypothesisProof(
                                    newObligation,
                                    usedHypotheses));
                    }
                }
            }

        }

        TheoremProverObligation newObligation;
        Proof proof;
        boolean underHypothesisProof = false;

        if (hypothesisUsed) {
            newObligation = new TheoremProverObligation(newFormula, obligationInput);
            newObligation.markHypothesesAsUsed(usedHypotheses);

            proof = new SymbolicOutermostEvaluationUnderHypothesisProof(newObligation, usedHypotheses);

            underHypothesisProof = true;
        }
        else {
            newObligation = new TheoremProverObligation(newFormula, obligationInput);
            proof = new SymbolicOutermostEvaluationProof(newObligation);
        }

        if(underHypothesisProof){
            return ResultFactory.proved(newObligation, YNMImplication.SOUND, proof);
        }
        else{
            return ResultFactory.proved(newObligation, YNMImplication.EQUIVALENT, proof);
        }

    }

    protected Formula evaluate(Program program, Formula formula,
            Set<HypothesisPair> hypotheses) {

        Formula newFormula = FormulaOutermostEvaluationVisitor.apply(formula, program);

        // TODO XTD change to outermost application ?
        if (!hypotheses.isEmpty()) {
            newFormula = FormulaEvaluationUnderHypothesisVisitor.apply(program,
                    newFormula, hypotheses);
        }

        if (newFormula.equals(formula)) {
            return formula;
        }
        else {
            return this.evaluate(program, newFormula, hypotheses);
        }

    }
}
