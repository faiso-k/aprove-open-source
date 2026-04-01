package aprove.verification.oldframework.IntegerReasoning.processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.IntegerReasoning.IntegerRuleSetProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Transforms an integer rule set to an ITRS.
 * @author cryingshadow
 * @version $Id$
 */
public class IntegerRuleSetToITRSProcessor extends Processor.ProcessorSkeleton {

    /**
     * @param iRules The integer rule set.
     * @return The corresponding ITRS.
     */
    public static ITRSProblem transformToITRS(Set<IGeneralizedRule> iRules) {
        Set<GeneralizedRule> rules = IGeneralizedRule.removeConditions(iRules);
        Set<TRSFunctionApplication> lhss = new LinkedHashSet<TRSFunctionApplication>();
        for (GeneralizedRule rule : rules) {
            lhss.add(rule.getLeft());
        }
        IQTermSet q = new IQTermSet(new QTermSet(lhss), IDPPredefinedMap.DEFAULT_MAP);
        return ITRSProblem.create(rules, q);
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof IntegerRuleSetProblem) {
            IntegerRuleSetProblem problem = (IntegerRuleSetProblem)obl;
            switch (problem.getRewritePosition()) {
                case INNERMOST:
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
                IntegerRuleSetToITRSProcessor.transformToITRS(problem.getRules()),
                problem.getRewritePosition() == IntegerRuleSetRewritePosition.INNERMOST ?
                    YNMImplication.EQUIVALENT :
                        YNMImplication.SOUND,
                new Proof.DefaultProof() {

                    @Override
                    public String export(Export_Util o, VerbosityLevel level) {
                        return "Transformed rule set to ITRS.";
                    }

                }
            );
    }

}
