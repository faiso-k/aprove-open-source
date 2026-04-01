package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Visitors.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;

/**
 * Conditional rewriting processor searches for all position
 * where condition rules could get applied.
 * Then constructs new COND obligations forcing that the conditions of a rule
 * have to be proved.
 * To make proving the conditions more easyly the condition gets equipped
 * with a big context.
 *
 * When the conditions get check they will be implicitly all quantified.
 * Actually, we would suffy to find only one solution because for rewriting we are looking for a matcher.
 * But this matching problem could not be solved by symbolic evaluation.
 *
 * @author dickmeis
 * @version $Id$
 */
@NoParams
public class ConditionalRewritingProcessor extends TheoremProverProcessor {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof TheoremProverObligation) {
            // even for indirect proofs
            return true;
        }
        return false;
    }

    @Override
    protected Result process(TheoremProverObligation obligationInput,
            BasicObligationNode obligationNode, Abortion aborter,
            RuntimeInformation rti) throws AbortionException {

        Program program = obligationInput.getProgram();

        Formula formula = obligationInput.getFormula();

        List<Pair<Formula, Formula>> newFormulas = ConditionalRewritingVisitor.apply(
                formula, program);

        if (newFormulas == null || newFormulas.isEmpty()) {
            return ResultFactory.notApplicable();
        }

        List<BasicObligationNode> resultingPositions =
            new ArrayList<BasicObligationNode>(2*newFormulas.size());
        Collection<ObligationNode> condNodes =
            new ArrayList<ObligationNode>(newFormulas.size());
        List<Pair<TheoremProverObligation, TheoremProverObligation>> newObligations =
            new ArrayList<Pair<TheoremProverObligation, TheoremProverObligation>>(newFormulas.size());

        for (Pair<Formula, Formula> newFormula : newFormulas) {
            TheoremProverObligation condObligation = new TheoremProverObligation(
                    newFormula.x, obligationInput);
            condObligation.setIndirectProof(false);
            BasicObligationNode condObligationNode =
                new BasicObligationNode(condObligation);

            TheoremProverObligation newObligation = new TheoremProverObligation(
                    newFormula.y, obligationInput);
            BasicObligationNode newObligationNode =
                new BasicObligationNode(newObligation);

            Pair<TheoremProverObligation, TheoremProverObligation> p
                = new Pair<TheoremProverObligation, TheoremProverObligation>
                            (condObligation, newObligation);

            newObligations.add(p);

            resultingPositions.add(condObligationNode);
            resultingPositions.add(newObligationNode);
            ObligationNode oblNode = JunctorObligationNode.createCond(condObligationNode, newObligationNode);

            condNodes.add(oblNode);
        }

        ConditionalRewriteProof proof = new ConditionalRewriteProof(newObligations);

        // workaround till itarative processor works
        if(! obligationInput.isIndirectProof()){
            return ResultFactory.provedOrJunctorObligations(condNodes,
                    resultingPositions, YNMImplication.EQUIVALENT, proof);
        }
        else{
            return ResultFactory.provedAndJunctorObligations(condNodes,
                    resultingPositions, YNMImplication.EQUIVALENT, proof);
        }
    }

}
