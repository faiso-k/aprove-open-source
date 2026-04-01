package aprove.verification.oldframework.Bytecode.Processors.ToGraph;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.JBCProblem.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;

/**
 * Look for nontermination in the given termination graph.
 * @author Carsten Otto
 */
public class JBCNonTermProcessor extends Processor.ProcessorSkeleton {
    /**
     * @return true for a JBC TerminationGraph problem
     * @param obl some obligation that should be a JBC TerminationGraph problem
     */
    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return (obl instanceof JBCTerminationGraphProblem);
    }

    /**
     * Work on the given obligation.
     * @param obl a JBC TerminationGraph problem
     * @param oblNode ignored.
     * @param aborter some aborter
     * @param rti ignored.
     * @throws AbortionException as soon as the aborter kicks in.
     * @return a nontermination proof, if we are lucky
     */
    @Override
    public Result process(final BasicObligation obl,
            final BasicObligationNode oblNode, final Abortion aborter,
            final RuntimeInformation rti) throws AbortionException {
        if (!(obl instanceof JBCTerminationGraphProblem)) {
            return ResultFactory.unsuccessful();
        }
        final JBCTerminationGraphProblem problem = (JBCTerminationGraphProblem) obl;
        final TerminationGraph termGraph = problem.getGraph();

        if (termGraph.runNonTermWorkers(aborter)) {
            if (termGraph.getNontermWitness() != null) {
                return ResultFactory.disproved(new JBCNonTerminationProof(termGraph.getNontermWitness()));
            }
        }
        return ResultFactory.unsuccessful();
    }
}
