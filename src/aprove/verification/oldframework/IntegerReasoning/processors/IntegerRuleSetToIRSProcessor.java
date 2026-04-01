package aprove.verification.oldframework.IntegerReasoning.processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.IntegerReasoning.IntegerRuleSetProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Transforms an integer rule set to an IRS.
 * @author cryingshadow
 * @version $Id$
 */
public class IntegerRuleSetToIRSProcessor extends Processor.ProcessorSkeleton {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof IntegerRuleSetProblem) {
            IntegerRuleSetProblem problem = (IntegerRuleSetProblem)obl;
            switch (problem.getRewritePosition()) {
                case TOPMOST:
                case TOPANDINNERMOST:
                    return problem.onlyConstructorRewriting();
                default:
                    // fall through
            }
        }
        return false;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
    throws AbortionException {
        IntegerRuleSetProblem problem = (IntegerRuleSetProblem)obl;
        return
            ResultFactory.proved(
                new IRSProblem(problem.getRules()),
                problem.getRewritePosition() == IntegerRuleSetRewritePosition.TOPMOST ?
                    YNMImplication.EQUIVALENT :
                        YNMImplication.SOUND,
                new Proof.DefaultProof() {

                    @Override
                    public String export(Export_Util o, VerbosityLevel level) {
                        return "Transformed rule set to IRS.";
                    }

                }
            );
    }

}
