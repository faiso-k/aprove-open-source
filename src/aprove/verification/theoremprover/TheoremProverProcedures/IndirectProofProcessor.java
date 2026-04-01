package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;

/**
 * Instead of proving a formula its negation has to be disproven.
 *
 * @author dickmeis
 * @version $Id$
 *
 */
@NoParams
public class IndirectProofProcessor extends TheoremProverProcessor {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof TheoremProverObligation) {
            TheoremProverObligation theorem_obl = (TheoremProverObligation) obl;

            // it makes no senese to negate twice
            if (theorem_obl.isIndirectProof()){
                return false;
            }

            // hypotheses are not allowed
            // they have to get removed first
            Set<HypothesisPair> hypotheses = theorem_obl.getHypothesesAsSet();

            if(hypotheses != null && !hypotheses.isEmpty()){
                return false;
            }

            return true;
        }
        return false;
    }

    @Override
    protected Result process(TheoremProverObligation obligationInput,
            BasicObligationNode obligationNode, Abortion aborter,
            RuntimeInformation rti) throws AbortionException {

        Formula formula = obligationInput.getFormula();

        // to negated DNF
        Formula negFormula = Not.create(formula);

        TheoremProverObligation newObligation = new TheoremProverObligation(
                negFormula, obligationInput);
        newObligation.setIndirectProof(true);

        // as we do not have any hypotheses
        return ResultFactory.proved(newObligation, YNMImplication.ANTIVALENT,
                new IndirectProofProof(newObligation));

    }
}
