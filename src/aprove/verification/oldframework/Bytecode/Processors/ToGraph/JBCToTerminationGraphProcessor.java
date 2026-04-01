package aprove.verification.oldframework.Bytecode.Processors.ToGraph;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.JBCProblem.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Create the Termination Graph for the given JBC program and start state.
 * @author Carsten Otto
 */
public class JBCToTerminationGraphProcessor extends Processor.ProcessorSkeleton {
    /**
     * The proof that describes how we transformed the program into a graph.
     * @author cotto
     */
    public class JBCToTerminationGraphProof extends DefaultProof {
        /**
         * Create the proof.
         */
        JBCToTerminationGraphProof() {
            super();
            this.shortName = "JBCToGraph";
            this.longName = "JBCToTerminationGraphProof";
        }

        /**
         * Export the proof.
         * @param o some export util
         * @param level the verbosity level
         * @return a textual representation of the proof
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Constructed TerminationGraph.";
        }
    }

    /**
     * The arguments given to this processor.
     */
    private final JBCOptions arguments;

    /**
     * @param args an object holding information about the arguments that may be
     * defined in the strategy
     */
    @ParamsViaArgumentObject
    public JBCToTerminationGraphProcessor(final JBCOptions args) {
        this.arguments = args;
    }

    /**
     * @return true for a JBC problem
     * @param obl some obligation that should be a JBC problem
     */
    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return (obl instanceof JBCProblem);
    }

    /**
     * Work on the given obligation.
     * @param obl a JBC problem
     * @param oblNode ignored.
     * @param aborter some aborter
     * @param rti ignored.
     * @throws AbortionException as soon as the aborter kicks in.
     * @return the TerminationGraphProblem for given JBC problem
     */
    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        if (!(obl instanceof JBCProblem)) {
            return ResultFactory.unsuccessful();
        }
        final JBCProblem jbcProblem = (JBCProblem) obl;
        this.arguments.setRuntimeOptions(jbcProblem.getRuntimeOptions());

        // create a start state, a method graph with that state and a termination graph with that method graph
        final TerminationGraph termGraph = new TerminationGraph(this.arguments, jbcProblem.getGoal(), aborter);
        final State state = jbcProblem.createStartState(termGraph);

        FuzzyType returnType = state.getCurrentStackFrame().getMethod().getDescriptor().getReturnType();
        assert jbcProblem.getGoal() != HandlingMode.SizeComplexity || returnType != null;

        final MethodGraph methodGraph = MethodGraph.create(state, termGraph);
        termGraph.addStartGraph(methodGraph);

        final Node startNode = methodGraph.getStartNode();
        termGraph.addJob(new StateNodeExpanderStandard(methodGraph, startNode));

        if (termGraph.run()) {
            termGraph.cleanIRs();
            final Collection<MethodEndListener> callStatesWithoutReturns = termGraph.findMissingReturns(state);

            if (termGraph.getNontermWitness() == null && this.arguments.tryNontermProofs()) {
                IMethod startMethod = termGraph.getStartGraph().getParsedMethod();
                for (final Map.Entry<IMethod, Collection<MethodGraph>> e : termGraph
                    .getMethodGraphMap()
                    .entrySet())
                {
                    final IMethod pm = e.getKey();
                    for (final MethodGraph mg : e.getValue()) {
                        if (mg.getMethodEndStates().isEmpty() && startMethod.equals(pm)) {
                            //main never returns. Oh noes!
                            termGraph.setNontermWitness(new NoReturnNonTermWitness(null, pm));
                        }
                    }
                }
            }
            if (termGraph.getNontermWitness() == null && this.arguments.tryNontermProofs()) {
                NoReturnNonTermWitnessFinder.checkForNonReturningMethods(termGraph, callStatesWithoutReturns, aborter);
            }

            if (termGraph.getNontermWitness() != null) {
                assert (this.arguments.tryNontermProofs());
                return ResultFactory.disproved(new JBCNonTerminationProof(termGraph.getNontermWitness()));
            } else {
                final JBCTerminationGraphProblem problem = new JBCTerminationGraphProblem(termGraph);
                return ResultFactory.proved(problem, jbcProblem.getGoal().equivalent(true), new JBCToTerminationGraphProof());
            }
        }
        return ResultFactory.unsuccessful();
    }
}
