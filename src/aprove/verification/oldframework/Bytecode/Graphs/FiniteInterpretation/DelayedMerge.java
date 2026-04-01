package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;

import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This class provides the method delayMerge that can be used to guess if we want to delay the otherwise enforced merge
 * of a state.
 *
 * 1) Find the node which is the first previous occurrence of the opcode of the state that should be merged. This most
 * often is the ndoe that we would merge with. During this merge all nodes below ("siblings" of the new state in paths
 * running parallel to the one that just finished) would be deleted.
 * 2) Find the nodes below the node found in step 1) which are still part of an ongoing computation.
 * 3) If such nodes exist and it looks like it is worth it to wait for the corresponding computations to finish (each
 * most likely resulting in a similar merge), delay the merge of the current node and instead (later) merge with the
 * leaves found in step 2). Then, with state resulting out of all the delayed merges, do the standard merge.
 *
 * The idea here is to not throw away work that is already done in parallel.
 *
 * See bug #30
 * @author cotto
 */
public class DelayedMerge {
    /**
     * Only call with held read lock on the graph!
     * @param expandedStateNode the state expanded to newState
     * @param candidates other nodes with which we would try to merge newState
     * @param newState the state expanded from newState, normally enforcing a merge
     * @param methodGraph the method graph we are working on
     * @return true if we want to delay the merge of newState
     */
    static boolean delayMerge(final Node expandedStateNode,
        final Collection<Node> candidates,
        final State newState,
        final MethodGraph methodGraph) {
        // find the shortest path from expandedStateNode to any candidate
        final Node minPred = DelayedMerge.getMinPred(expandedStateNode, candidates, methodGraph);

        if (minPred == null) {
            // we did not find an immediate predecessor node (with which we would normally merge)
            return false;
        }

        // now find all "open ends" below the predecessor
        final Collection<Node> leaves = DelayedMerge.findLeaves(minPred, methodGraph);

        assert (leaves.contains(expandedStateNode));

        if (leaves.size() == 1) {
            // nothing to do here, just do a standard merge
            return false;
        }

        // just have a look at the leaves that may end in the opcode of the state to merge
        final Collection<Node> goodLeaves = DelayedMerge.getGoodLeaves(leaves, newState);

        if (goodLeaves == null) {
            // we may decide that it is not worth it to wait for the leaves
            return false;
        }

        assert (goodLeaves.contains(expandedStateNode));

        if (goodLeaves.size() == 1) {
            // nothing to do here, just do a standard merge
            return false;
        }

        return true;
    }

    /**
     * @param leaves the computed leaves (cf. findLeaves).
     * @param newState the state that should be merged
     * @return null if it is not worth waiting for the leaves. Otherwise the leaves are returned that may eventually
     * result in a state with the same opcode as newState.
     */
    private static Collection<Node> getGoodLeaves(final Collection<Node> leaves, final State newState) {
        final Collection<Node> goodLeaves = new LinkedHashSet<>();

        final OpCode opCode = newState.getCurrentOpCode();
        final IMethod method = newState.getCurrentStackFrame().getMethod();

        int distances = 0;
        for (final Node leaf : leaves) {
            final State state = leaf.getState();
            /*
             * We may have stack frames of methods on top that need to finish before we come to the opcode that
             * will be merged. Ignore these and find the current opcode in the "interesting" method (which
             * hopefully leads to the opcode of the merge).
             */

            // top is first entry
            for (final StackFrame frame : state.getCallStack().getStackFrameList()) {
                if (frame.getMethod().equals(method)) {
                    final OpCode currentOpCode = frame.getCurrentOpCode();
                    final int distance = currentOpCode.mayReach(opCode);
                    if (distance >= 0) {
                        distances += distance;
                        goodLeaves.add(leaf);
                    }
                    break;
                }
            }
        }
        if (distances > 50) {
            return null;
        }

        return goodLeaves;
    }

    /**
     * @param minPred the predecessor node somewhere above the state that should be merged
     * @param methodGraph the method graph we are working on
     * @return the nodes below minPred that do not have a successor and are no "end" nodes, i. e. the open ends of the
     * computation.
     */
    private static Collection<Node> findLeaves(final Node minPred, final MethodGraph methodGraph) {
        final LinkedList<Node> todo = new LinkedList<>();
        final Collection<Node> seen = new LinkedHashSet<>();
        final Collection<Node> leaves = new LinkedHashSet<>();
        todo.add(minPred);
        while (!todo.isEmpty()) {
            final Node current = todo.pop();
            if (!seen.add(current)) {
                continue;
            }
            boolean foundEdge = false;
            for (final Edge out : current.getOutEdges()) {
                if (out.getLabel() instanceof DebugEdge) {
                    continue;
                }
                foundEdge = true;
                todo.add(out.getEnd());
            }
            if (!foundEdge) {
                leaves.add(current);
            }
        }

        // remove the leaves that are done
        final Iterator<Node> it = leaves.iterator();
        while (it.hasNext()) {
            final Node current = it.next();
            if (current.getState().callStackEmpty()) {
                it.remove();
            }
        }
        return leaves;
    }

    /**
     * @param expandedStateNode the node that evaluated to the node that should be merged
     * @param candidates the nodes with which we normally would try to merge
     * @param methodGraph the method graph we are working on
     * @return null if unsuccessful, otherwise a predecessor of expandedStateNode that is a valid merge partner (and not
     * a state resulting of a still delayed merge)
     */
    private static Node getMinPred(final Node expandedStateNode,
        final Collection<Node> candidates,
        final MethodGraph methodGraph) {

        Pair<Node, Integer> minPred = null;
        final LinkedList<Pair<Node, Integer>> todo = new LinkedList<>();
        todo.add(new Pair<>(expandedStateNode, 0));
        final Collection<Node> seen = new LinkedHashSet<>();
        while (!todo.isEmpty()) {
            final Pair<Node, Integer> current = todo.pop();
            final Node currentNode = current.x;
            final Integer distance = current.y;
            if (!seen.add(currentNode)) {
                continue;
            }
            if (candidates.contains(currentNode)) {
                if (minPred == null || minPred.y > distance) {
                    minPred = current;
                }
            } else {
                for (final Edge in : currentNode.getInEdges()) {
                    if (in.getLabel() instanceof DebugEdge) {
                        continue;
                    }
                    if (in.getLabel() instanceof MethodSkipEdge) {
                        continue;
                    }
                    todo.add(new Pair<>(in.getStart(), distance + 1));
                }
            }
        }

        if (minPred != null) {
            return minPred.x;
        }
        return null;
    }
}
