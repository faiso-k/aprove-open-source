package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Implication;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;

/**
 * This Processor generalises a formula of the form a->b to
 * (a<->b)
 * @author rabe
 */
@NoParams
public class InverseSplittingProcessor extends TheoremProverProcessor {

    @Override
    protected Result process(TheoremProverObligation obligationInput, BasicObligationNode obligationNode, Abortion aborter,
            RuntimeInformation rti) throws AbortionException {

        // get formula and program
        Program program = obligationInput.getProgram();
        Formula formula = obligationInput.getFormula();

        if(formula.isImplication()) {

            boolean apply = false;
            Implication implication = (Implication)formula;

            // check for mutal recursive functions
            Set<DefFunctionSymbol> functionSymbolsRightHandSide = implication.getAllDefFunctionSymbols();
            for(DefFunctionSymbol defFunctionSymbol : implication.getLeft().getAllDefFunctionSymbols()) {

                Set<DefFunctionSymbol> mutualRecursiveFunctions = program.getMutualRecursiveFunctions(defFunctionSymbol, false);
                mutualRecursiveFunctions.retainAll(functionSymbolsRightHandSide);
                if(mutualRecursiveFunctions.size() > 0) {
                    apply = true;
                    break;
                }
            }

            if(apply) {

                // create new formula
                Formula newFormula = Equivalence.create(implication.getLeft(),implication.getRight());


                // if this position is reached processor is not or is not anymore applicable
                TheoremProverObligation newObligation = new TheoremProverObligation(newFormula,obligationInput);
                return ResultFactory.proved(newObligation, YNMImplication.SOUND, new InverseSplittingProof(newObligation));

            }else{
                return ResultFactory.notApplicable();
            }

        }else{
            return ResultFactory.notApplicable();
        }

    }

}
