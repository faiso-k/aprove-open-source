/**
 * scetch for ConditionalRewritingProcessor when the ItearativeProcessor can be used
 *
 * meanwhile a workaround is used
 */


package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.UserStrategies.*;
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

public class ConditionalRewritingIterativeProcessor extends Processor.ProcessorSkeleton {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof TheoremProverObligation) {
            // even for indirect proofs
            return true;
        }
        return false;
    }

    @Override
    public Result process(BasicObligation obligationInp,
            BasicObligationNode obligationNode, Abortion aborter,
            RuntimeInformation rti) {

        TheoremProverObligation obligationInput = (TheoremProverObligation) obligationInp;

        Program program = obligationInput.getProgram();

        Formula formula = obligationInput.getFormula();

        List<Pair<Formula, Formula>> newFormulas = ConditionalRewritingVisitor.apply(
                formula, program);


        if (newFormulas == null) {
            return ResultFactory.unsuccessful();
        }

        List<ExecutableStrategy> results = new ArrayList<ExecutableStrategy>(newFormulas.size());

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

            ObligationNode oblNode = JunctorObligationNode.createCond(condObligationNode, newObligationNode);

            VariableStrategy variableStrategy = new VariableStrategy("main");

            List<ExecutableStrategy> stratList = new ArrayList<ExecutableStrategy>(2);
            stratList.add(variableStrategy.getExecutableStrategy(condObligationNode, rti));
            stratList.add(variableStrategy.getExecutableStrategy(newObligationNode, rti));

            ExecutableStrategy execStrategy = new ExecAllSequential(stratList, rti);

            ConditionalRewriteIterativeProof proof = new ConditionalRewriteIterativeProof(p);

            Result res = ResultFactory.provedWithNewStrategy(oblNode, YNMImplication.EQUIVALENT, proof, execStrategy);

            results.add(new ExecResult(rti, obligationNode, res));
        }

        ExecutableStrategy resultStr = ExecFirst.createFromExec(results, obligationNode, rti);
        return ResultFactory.justANewStrategy(resultStr);
    }
}
