package aprove.verification.dpframework.TRSProblem.Utility;

import java.util.*;

import aprove.verification.oldframework.Utility.Graph.*;

/**
 * help-class capturing objects for building the OutermostTerminationGraph
 *
 * @author Sebastian Weise
 */

public class Desktop {

    // the next Index-Value to use for Metavariables
    private final MyInteger toUseNext;
    // the number of so far created Nodes of the Graph
    private final MyInteger countCreatedNodes;
    // the "Front" of our Graph containing all the Undefined-Nodes
    private final Queue<Node<NodeEntry>> front;
    /*
     * (maximal) Equivalence-Classes of Nodes for the ReUse-Heuristic;
     * all Nodes in a Class are equivalent to each other and
     *      are Target-Nodes for the ReUse-Heuristic;
     * the empty set must never be contained!
     */
    private final Set<Set<Node<NodeEntry>>> equivalenceClasses;

    public Desktop() {
        this.toUseNext =
            new MyInteger(OutermostTerminationGraph.START_NUMBER);
        this.countCreatedNodes = new MyInteger(0);
        this.front = new LinkedList<Node<NodeEntry>>();
        this.equivalenceClasses = new LinkedHashSet<Set<Node<NodeEntry>>>();
    }

    public MyInteger getToUseNext() {
        return this.toUseNext;
    }

    public MyInteger getCountCreatedNodes() {
        return this.countCreatedNodes;
    }

    public Queue<Node<NodeEntry>> getFront() {
        return this.front;
    }

    /**
     * @return the corresponding Equivalence Class of "node" and null if none exists so far
     */
    public Set<Node<NodeEntry>> getEquivalenceClass(final Node<NodeEntry> node) {
        for (final Set<Node<NodeEntry>> actClass : this.equivalenceClasses) {
            if (node.getObject().isEquivalent(
                actClass.iterator().next().getObject())) {
                return actClass;
            }
        }
        return null;
    }

    /**
     * creates a new Equivalence-Class containing (so far exactly) "node",
     *      so "node" must not belong to any so far existing Equivalence Class!
     */
    public void createNewEquivalenceClass(final Node<NodeEntry> node) {
        final Set<Node<NodeEntry>> newClass =
            new LinkedHashSet<Node<NodeEntry>>();
        newClass.add(node);
        this.equivalenceClasses.add(newClass);
    }
}