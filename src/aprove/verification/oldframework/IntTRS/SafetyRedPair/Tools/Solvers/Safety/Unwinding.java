package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Safety;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.LinearTransitionPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Debug.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Interpolation.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Safety.Tree.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Safety.Tree.Vertex.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;


/**
 * Attempts to prove safety of a program graph using interpolation
 * @author marinag
 */
public class Unwinding {
    /**
     * Original program graph
     */
    private final LinearProgramGraph graph;

    /**
     * Unwinding tree of the program graph
     */
    private final UnwindingTree tree;

    /**
     * Unwinding process result
     */
    private UnwindingResult result;

    /**
     * Aborter
     */
    private final Abortion aborter;

    /**
     * Unwinding result, contains the final tree
     * @author marinag
     */
    public static class UnwindingResult {
        public UnwindingResult(final UnwindingTree tree) {
            this.tree = tree;
        }

        private final UnwindingTree tree;

        public UnwindingTree getTree() {
            return this.tree;
        }

        @Override
        public String toString() {
            return this.getClass().getSimpleName();
        }
    }

    /**
     * Safe result
     * @author marinag
     */
    public static class Safe extends UnwindingResult {
        public Safe(final UnwindingTree tree) {
            super(tree);
        }
    }

    /**
     * Unsafe result, includes also the error vertex that could not be disproved
     * @author marinag
     */
    public static class Unsafe extends UnwindingResult {

        private final Vertex errorVertex;
        private List<Edge<LinearTransitionPair, LocationID>> errorPath;

        public Unsafe(final UnwindingTree tree, final Vertex errorVertex) {
            super(tree);
            assert (errorVertex != null);
            this.errorVertex = errorVertex;
        }

        public Vertex getErrorVertex() {
            return this.errorVertex;
        }

        public List<Edge<LinearTransitionPair, LocationID>> getErrorPath() {
            if (this.errorPath == null) {
                final List<Edge<LinearTransitionPair, LocationID>> path = new ArrayList<>();

                for (final Node<VertexID> v : this.getTree().getAncestorsInclusive(this.errorVertex)) {
                    if (this.getTree().isRoot(v)) {
                        continue;
                    }

                    path.add(((Vertex) v).getProgramEdge());
                }

                this.errorPath = ImmutableCreator.create(path);
            }

            return this.errorPath;
        }

        @Override
        public String toString() {
            return super.toString() + ": " + this.errorVertex.toString();
        }
    }

    /**
     * @param programGraph program graph
     * @param aborter aborter
     */
    public Unwinding(final ProgramGraph programGraph, final Abortion aborter) {
        this.graph = new LinearProgramGraph(programGraph);
        this.tree = UnwindingTree.create(this.graph, aborter);
        this.aborter = aborter;
    }

    public Unwinding(final LinearProgramGraph LinearProgramGraph, final Abortion aborter) {
        this.graph = LinearProgramGraph;
        this.tree = UnwindingTree.create(this.graph, aborter);
        this.aborter = aborter;
    }

    public Unwinding(
        final LinearProgramGraph LinearProgramGraph,
        final Abortion aborter,
        final InterpolationSolver interpolationSolver)
    {
        this.graph = LinearProgramGraph;
        final InterpolationSolver solver = interpolationSolver;
        this.tree = UnwindingTree.create(this.graph, solver, aborter);
        this.aborter = aborter;
    }

    /**
     * @return attempts to unwind the tree as long as it contains uncovered leaves, and no error location was failed to disprove.
     */
    public UnwindingResult unwind() {
        Vertex v = null;

        while (this.result == null && (v = this.tree.getUncoveredLeaf()) != null) {
            final Vertex errV = this.dfs(v);

            if (errV != null) {
                this.result = new Unsafe(this.tree, errV);
            }
        }

        if (this.result != null) {
            return this.result;
        }

        return new Safe(this.tree);
    }

    /**
     * @param node the vertex to be expanded
     * @return the newly added leaves due to the expansion
     */
    public List<Vertex> expand(final Vertex node) {
        final Vertex v = node;
        assert (!v.isFalseLabel() && !this.tree.isCovered(node) && this.tree.isLeaf(node));
        final Location loc = v.getLocation();
        final List<Vertex> children = new LinkedList<>();

        if (loc instanceof ReturnLocation) {
            final Vertex child =
                this.tree.addChild(v, new Edge<>(v.getLocation(), v.getReturnLocation(), new LinearTransitionPair(
                    LinearConstraintsSystem.create())));
            return this.expand(child);
        }

        if (this.graph.contains(loc)) {

            final List<Edge<LinearTransitionPairsSet, LocationID>> childTransitions = new ArrayList<>(); //this.graph.getOutEdges(loc));

            for (final Edge<LinearTransitionPairsSet, LocationID> e : this.graph.getOutEdges(loc)) {

                int i = 0;

                while (i < childTransitions.size() && childTransitions.get(i).getEndNode().compareTo(e.getEndNode()) > 0) {
                    i++;
                }

                childTransitions.add(i, e);

            }

            for (final Edge<LinearTransitionPairsSet, LocationID> e : new ArrayList<>(childTransitions)) {
                if (e.getStartNode().equals(e.getEndNode())) {
                    childTransitions.remove(e);
                    childTransitions.add(e);
                }
            }

            for (final Edge<LinearTransitionPairsSet, LocationID> t : childTransitions) {
                for (final Edge<LinearTransitionPair, LocationID> sE : LinearProgramGraph.splitEdge(t)) {
                    children.add(this.tree.addChild(v, sE));
                }
            }
        }

        if (children.isEmpty()) {
            children.add(this.tree.addChild(
                v,
                new Edge<>(
                    v.getLocation(),
                    v.getLocation(),
                    new LinearTransitionPair(
                        LinearConstraintsSystem.create()))));
        }

        return children;
    }



    /**
     * @param v currently examined vertex
     * @return Unsafe in case failed to disprove an error location, null otherwise
     */
    private Vertex dfs(final Vertex v) {
        this.aborter.checkAbortion();
        List<Vertex> children = new LinkedList<>();

        if (!v.isFalseLabel()
            && !this.tree.isCovered(v)
            && !this.tree.close(v, this.aborter))

        {
            if (!this.tree.isRoot(v)) {
                Log.report("dfs", this.tree.getInEdge(v).toString());
            }

            if (v.getLocation() instanceof AbortLocation) {
                if (!this.tree.forceClose(v, this.aborter) && !this.tree.refinePathTo(v, this.aborter, true))
                {

                    for (final Node<VertexID> an : this.tree.getAncestors(v)) {
                        final Vertex a = (Vertex) an;
                    }

                    this.result = new Unsafe(this.tree, v);
                    return v;
                }

                final List<Node<VertexID>> anc = this.tree.getAncestors(v);
                Collections.reverse(anc);

                for (final Node<VertexID> a : anc) {
                    final Vertex u = (Vertex) a;

                    if (!u.isFalseLabel()) {
                        break;
                    }
                }

                assert v.isFalseLabel();
                return null;
            } else if (v.isFalseTransition()) {

                if (this.tree.forceClose(v, this.aborter) || this.tree.refinePathTo(v, this.aborter, false)) {
                    return null;
                }
            }

            if (!this.tree.forceClose(v, this.aborter)) {
                if (!v.isFalseLabel()) {
                    children = this.expand(v);
                }
                for (final Vertex child : children) {
                    final Vertex u = this.dfs(child);

                    if (u != null) {
                        return u;
                    }
                }
            }
        }
        return null;
    }


    /**
     * @return Unsafe in case failed to disprove an error location, Safe otherwise
     */
    public UnwindingResult getResult() {
        if (this.result == null) {
            this.result = this.unwind();
        }

        return this.result;
    }

    private boolean foundErrorLocation() {
        return this.result != null && this.getResult() instanceof Unsafe;
    }


    public InterpolationSolver getInterpolationSolver() {
        return this.tree.getInterpolationSolver();
    }
}
