package aprove.verification.oldframework.Bytecode.Consistency;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;

/**
 * Checks that inside a MethodGraph all method calls have a certain structure.
 * The exact semantics is documented inside {@link #check()}
 * @author Fabian K&uuml;rten
 * @see OutEdgeTypes a similar check
 */
public class MethodStartStructure implements Checker {

    /**
     * The method graph to perform the checks on.
     */
    private final MethodGraph graph;

    /**
     *Any node which caused a failure to appear.
     */
    private Node firstFailNode;

    /**
     * A more detailed error message.
     */
    private String message;

    /**
     * Creates the checker.
     * @param graph the graph to check on
     */
    public MethodStartStructure(final MethodGraph graph) {
        this.graph = graph;
    }

    @Override
    public boolean check() {
        this.graph.getGraphLock().readLock().lock();
        try {
            for (final Edge outerEdge : this.graph.getEdges()) {
                if (outerEdge.getLabel() instanceof MethodStartEdge) {
                    /*
                     * Either:
                     * A method start edge has only CallAbstract and MethodSkip successors.
                     * If there is a successor, then there is a CallAbstract successor.
                     * Or: The evaluation is inline, in this case there are no CallAbstract or MethodSkip successors
                     */
                    // Middle node is the SUCCESSOR
                    final Node middle = outerEdge.getEnd();
                    final Set<Edge> innerEdges = middle.getOutEdges();

                    if (innerEdges.size() == 0) {
                        // pass, we might still be in expansion
                        continue;
                    }
                    int callAbstractEdges = 0;
                    boolean methodSkipSuccessor = false;
                    boolean failedIntersectionSuccessor = false;
                    boolean normalSuccessors = false;
                    for (final Edge innerEdge : innerEdges) {
                        if (innerEdge.getLabel() instanceof CallAbstractEdge) {
                            callAbstractEdges++;
                        } else if (innerEdge.getLabel() instanceof MethodSkipEdge) {
                            methodSkipSuccessor = true;
                        } else if (innerEdge.getLabel() instanceof FailedIntersectionEdge) {
                            failedIntersectionSuccessor = true;
                        } else {
                            // normal successor
                            normalSuccessors = true;
                        }
                    }
                    // Now make sure that there is exactly one CallAbstractEdge
                    if ((callAbstractEdges > 0 || methodSkipSuccessor || failedIntersectionSuccessor)
                        && normalSuccessors)
                    {
                        // There may not be both normal and special
                        this.firstFailNode = middle;
                        this.message = "Mixed successors.";
                        return false;
                    }
                    if (methodSkipSuccessor && callAbstractEdges != 1) {
                        this.firstFailNode = middle;
                        this.message = "MethodSkipSuccessor implies exactly one CallAbstractEdge.";
                        return false;
                    }
                    if (callAbstractEdges > 1) {
                        this.firstFailNode = middle;
                        this.message = "More than one CallAbstractEdge.";
                        return false;
                    }
                } else if (outerEdge.getLabel() instanceof CallAbstractEdge) {
                    /*
                     * A CallAbstractEdge may only have a single instance
                     * successor inside THIS graph (and exactly one meta-edge to
                     * another graph).
                     *
                     * The predecessor has exactly one MethodStartEdge predecessor
                     * (and else only instance predecessors).
                     */
                    // Middle node is the PREDECESSOR
                    final Node pred = outerEdge.getStart();
                    if (!MethodStartStructure.checkPred(pred)) {
                        this.firstFailNode = pred;
                        return false;
                    }
                    // Now check for successor stuff
                    final Node succ = outerEdge.getEnd();
                    final Set<Edge> succEdges = succ.getOutEdges();
                    if (succEdges.size() > 1) {
                        this.firstFailNode = succ;
                        return false;
                    } else if (succEdges.size() == 1) {
                        /*
                         * If we have a successor, it must be an instance successor.
                         */
                        if (!(succEdges.iterator().next().getLabel() instanceof InstanceEdge)) {
                            this.firstFailNode = succ;
                            return false;
                        }
                    }
                } else if (outerEdge.getLabel() instanceof MethodSkipEdge) {
                    /*
                     * Similar check for predecessors.
                     * No constraint on successors for now.
                     */
                    final Node pred = outerEdge.getStart();
                    if (!MethodStartStructure.checkPred(pred)) {
                        this.firstFailNode = pred;
                        return false;
                    }
                } else {
                    // ignore these edge types for now
                    continue;
                }
            } // loop over all edges
            return true;
        } finally {
            this.graph.getGraphLock().readLock().unlock();
        }
    }

    /**
     * Checks the predecessors of the node. In particular, there must be exactly
     * one incoming {@link MethodStartEdge} and all other edges must be
     * {@link InstanceEdge}
     * @param node the node to check
     * @return iff the check is passed
     */
    private static boolean checkPred(final Node node) {
        final Set<Edge> predEdges = node.getInEdges();
        if (predEdges.size() == 0) {
            /*
             * fail, there must be a predecessor
             * (albeit this should be detected by other checks)
             */
            return false;
        }
        int methodStartEdges = 0;
        for (final Edge innerEdge : predEdges) {
            if (innerEdge.getLabel() instanceof MethodStartEdge) {
                methodStartEdges++;
            } else if (innerEdge.getLabel() instanceof InstanceEdge) {
                // fine
                continue;
            } else {
                // fail
                return false;
            }
        }
        // Now make sure that there is exactly one MethodStartEdge
        if (methodStartEdges != 1) {
            return false;
        }
        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        if (this.firstFailNode == null) {
            return "Check passed.";
        } else {
            return this.firstFailNode.toString()
                + " has inconsistent edge structure"
                + (this.message != null ? this.message : "");
        }
    }
}
