package aprove.verification.oldframework.IRSwT.Processors.TraceTermination;

import java.util.*;

import aprove.verification.oldframework.IRSwT.Digraph.*;

/**
 * Represents a finite automaton.
 * @author Matthias Hoelzel
 */
public class FiniteAutomaton {
    /** An edge-labeled digraph. */
    private final LabeledDigraph<String, String> transitionStructure;

    /** Set of final states. */
    private final LinkedHashSet<String> finalStates;

    public FiniteAutomaton() {
        this.transitionStructure = new LabeledDigraph<>();
        this.finalStates = new LinkedHashSet<>();
    }

    public void addState(final String s) {
        this.transitionStructure.addVertex(s);
    }

    public void addFinalState(final String s) {
        this.finalStates.add(s);
        this.transitionStructure.addVertex(s);
    }

    public void addTransition(final String source, final String toRead, final String destination) {
        this.addState(source);
        this.addState(destination);
        this.transitionStructure.connect(source, destination, toRead);
    }

    public boolean hasTransition(final String source, final String toRead, final String destination) {
        if (!this.transitionStructure.isConnected(source, destination)) {
            return false;
        } else {
            return this.transitionStructure.getLabels(source, destination).contains(toRead);
        }
    }

    public LinkedHashSet<String> simulate(final String startState, final LinkedList<String> input) {
        final LinkedHashSet<String> currentStates = new LinkedHashSet<>();
        currentStates.add(startState);
        return this.simulate(currentStates, input);
    }

    public LinkedHashSet<String> simulate(final LinkedHashSet<String> startStates, final LinkedList<String> input) {
        LinkedHashSet<String> currentStates = startStates;
        for (final String a : input) {
            final LinkedHashSet<String> nextStates = new LinkedHashSet<>();
            for (final String s : currentStates) {
                for (final String n : this.transitionStructure.getNeighbors(s)) {
                    if (this.transitionStructure.getLabels(s, n).contains(a)) {
                        nextStates.add(n);
                    }
                }
            }
            currentStates = nextStates;
        }
        return currentStates;
    }

    public boolean accepts(final String startState, final LinkedList<String> input) {
        return this.containsFinalState(this.simulate(startState, input));
    }

    public boolean accepts(final LinkedHashSet<String> startStates, final LinkedList<String> input) {
        return this.containsFinalState(this.simulate(startStates, input));
    }

    public boolean acceptsPrefix(final LinkedHashSet<String> startStates, final LinkedList<String> input) {
        final LinkedHashSet<String> states = this.simulate(startStates, input);
        return this.canReachFinalState(states);
    }

    public boolean acceptsPrefix(final String startState, final LinkedList<String> input) {
        final LinkedHashSet<String> states = this.simulate(startState, input);
        return this.canReachFinalState(states);
    }

    private boolean canReachFinalState(final LinkedHashSet<String> states) {
        boolean changed;
        do {
            changed = false;
            for (final String s : this.transitionStructure.getVertices()) {
                for (final String t : this.transitionStructure.getNeighbors(s)) {
                    if (!states.contains(t)) {
                        states.add(t);
                        changed = true;
                    }
                }
            }

        } while (changed);
        return this.containsFinalState(states);
    }

    private boolean containsFinalState(final LinkedHashSet<String> states) {
        for (final String finalState : this.finalStates) {
            if (states.contains(finalState)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        sb.append(this.transitionStructure.toString());
        sb.append("\nFinal states: ");
        sb.append(this.finalStates);
        return sb.toString();
    }
}
