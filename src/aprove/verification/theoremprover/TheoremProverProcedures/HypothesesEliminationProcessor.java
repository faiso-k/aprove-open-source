package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;

/**
 * Removes all hypotheses.
 * So the indirect proof processor is applicable.
 *
 * @author dickmeis
 * @version $Id$
 *
 */
@NoParams
public class HypothesesEliminationProcessor extends TheoremProverProcessor {

    @Override
    protected Result process(TheoremProverObligation obligationInput,
            BasicObligationNode obligationNode, Abortion aborter,
            RuntimeInformation rti) throws AbortionException {

        Set<HypothesisPair> hypotheses = obligationInput.getHypothesesAsSet();

        if(hypotheses.isEmpty()){
            return ResultFactory.notApplicable("There are no hypotheses to remove.");
        }

        TheoremProverObligation newObl = obligationInput.deepcopy();

        // removes all hypotheses
        newObl.setHypotheses(new HashMap<HypothesisPair, Integer>());

        return ResultFactory.proved(newObl ,
                YNMImplication.SOUND,
                new HypothesesEliminationProof(hypotheses));

    }
}
