package aprove.verification.oldframework.Bytecode.Processors.ToGraph;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Checks a completed termination graph contains method graphs that do not contain any return nodes.
 * If yes, it tries to prove that these method graphs are actually called in the program.
 *
 * @author Marc Brockschmidt
 */
public final class NoReturnNonTermWitnessFinder {
    /**
     * Constructor that you should not use.
     */
    private NoReturnNonTermWitnessFinder() {
        assert false : "Thou shall not instantiate me!";
    }

    /**
     * @param termGraph the termination graph to check (has to be finished!)
     * @param aborter the aborter, used to check if we still need to run
     * @throws AbortionException if we were aborted.
     */
    public static void checkForNonReturningMethods(final TerminationGraph termGraph,
        final Collection<MethodEndListener> callStatesWithoutReturns,
        final Abortion aborter) throws AbortionException {
        //Do not continue if we already proved nontermination:
        if (termGraph.getNontermWitness() != null) {
            return;
        }

        for (final MethodEndListener mel : callStatesWithoutReturns) {
            //Oh noes, no return. Find a call site which is reachable:

            final IMethod nonTermMethod = mel.getNode().getState().getCurrentStackFrame().getMethod();
            if (Globals.DEBUG_MARC) {
                System.err.println(nonTermMethod + " never returns! Trying prove call site reachable...");
            }

            //Try to prove that we reach this call site:
            final MethodGraph callingGraph = mel.getMethodGraph();
            final Node callingNode = mel.getNode();

            final Collection<State> startStateWitnesses =
                WitnessUtilities.findStartStateWitnessesForState(callingGraph, callingNode, callingNode.getState(),
                    Collections.<AbstractVariableReference, Long>emptyMap(), true, aborter);

            for (final State startStateWitness : startStateWitnesses) {
                final Pair<List<State>, Triple<Integer, Integer, Set<StatePosition>>> run =
                    WitnessUtilities.verifyWitness(startStateWitness, callingNode.getState(), null, null, aborter,
                        termGraph.getJBCOptions());

                if (run != null) {
                    termGraph.setNontermWitness(new NoReturnNonTermWitness(run.x, nonTermMethod));
                    return;
                }
            }
        }
    }
}
