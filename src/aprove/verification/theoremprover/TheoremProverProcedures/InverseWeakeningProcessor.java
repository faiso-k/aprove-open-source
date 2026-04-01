package aprove.verification.theoremprover.TheoremProverProcedures;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Implication;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;


@NoParams
public class InverseWeakeningProcessor extends TheoremProverProcessor {

    @Override
    protected Result process(TheoremProverObligation obligationInput, BasicObligationNode obligationNode, Abortion aborter,
            RuntimeInformation rti) throws AbortionException {

        // this technique should not applied to implications
        // supported directly by the user
        if(!obligationInput.getFormula().isImplication()) {
            return ResultFactory.notApplicable();
        }

        Implication implication = (Implication)obligationInput.getFormula();

        for(Equation equation : implication.getLeft().getAllEquations()) {

            if(((equation.getLeft().getSymbol() instanceof ConstructorSymbol) && (equation.getRight().getSymbol() instanceof VariableSymbol))
                || ((equation.getLeft().getSymbol() instanceof VariableSymbol) && (equation.getRight().getSymbol() instanceof ConstructorSymbol)) ) {
                return ResultFactory.notApplicable();
            }

        }


        TheoremProverObligation newObligation = new TheoremProverObligation(implication.getRight(),obligationInput);
        return ResultFactory.proved(newObligation,YNMImplication.SOUND, new InverseWeakeningProof(newObligation));
    }

}