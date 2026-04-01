package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Safety.Tree;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.Disjunctions.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.LinearRelation.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.LinearTransitionPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Interpolation.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Safety.Tree.Vertex.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Unwinding tree, used for the Unwinding process
 * @author marinag
 */
public class UnwindingTree extends SimpleTree<VertexID, LinearConstraintsSystem> {

    protected final InterpolationSolver solver;

    final Map<FunctionSymbol, Set<String>> fSymToVar = new HashMap<>();
    final Map<String, Pair<TRSFunctionApplication, List<String>>> varToF = new HashMap<>();

    protected final LinearProgramGraph ug;
    protected Abortion aborter;

    public static Vertex toVertex(final Node<VertexID> node) {
        if (node instanceof Vertex) {
            return (Vertex) node;
        }
        throw new RuntimeException();
    }

    final Map<Vertex, Set<Vertex>> covered = new HashMap<>();
    final Map<Vertex, Vertex> covererMap = new HashMap<>();

    private int verticesCounter;


    private int getNextVertexId() {
        return this.verticesCounter++;
    }

    private UnwindingTree(final LinearProgramGraph graph, final Abortion aborter) {
        this(graph, InterpolationSolver.create(
            graph.getFSymToVars(),
            graph.getVarsToFApp(),
            graph.getFrshNameGenerator(),
            aborter), aborter);
    }

    public UnwindingTree(final LinearProgramGraph graph, final InterpolationSolver solver, final Abortion aborter) {
        this(graph.getStartLocation(), graph, solver, aborter);
    }

    private UnwindingTree(
        final Location root,
        final LinearProgramGraph graph,
        final InterpolationSolver solver,
        final Abortion aborter)
    {
        super(new Vertex(0, root, graph.getVarsToFApp()));

        this.getNextVertexId();
        this.addLocationVertex(UnwindingTree.toVertex(this.getRoot()));

        this.ug = graph;
        this.aborter = aborter;
        this.solver = solver;
    }

    private UnwindingTree(
        final Location root,
        final Vertex father,
        final LinearProgramGraph graph,
        final InterpolationSolver solver,
        final Abortion aborter)
    {
        super(new Vertex(0, root, father, graph.getVarsToFApp()));

        this.getNextVertexId();
        this.addLocationVertex(UnwindingTree.toVertex(this.getRoot()));

        this.ug = graph;
        this.aborter = aborter;
        this.solver = solver;
    }


    private static UnwindingTree create(
        final Location root,
        final LinearProgramGraph graph,
        final Vertex father,
        final InterpolationSolver solver,
        final Abortion aborter)
    {
        final UnwindingTree t =
            father == null ? new UnwindingTree(root, graph, solver, aborter) : new UnwindingTree(
                root,
                father,
                graph,
                solver,
                aborter);

            return t;
    }

    public static UnwindingTree create(
        final LinearProgramGraph graph,
        final InterpolationSolver solver,
        final Abortion aborter)
    {
        return new UnwindingTree(graph, solver, aborter);
    }

    public static UnwindingTree create(
        final LinearProgramGraph graph,
        final Abortion aborter)
    {
        return new UnwindingTree(graph, aborter);
    }



    public boolean isCovered(final Vertex v) {
        if (this.getCoverer(v) != null) {
            return true;
        }


        if (this.getFather(v) == null) {
            return false;
        }

        return this.isCovered(UnwindingTree.toVertex(this.getFather(v)));
    }

    private synchronized Vertex getCoverer(final Vertex v) {
        return this.covererMap.get(v);
    }

    public void removeDescendantsAllCovered(final Vertex vertex) {
        for (final Node<VertexID> v : this.getOut(vertex)) {
            this.removeAllCovered(UnwindingTree.toVertex(v));
            this.removeDescendantsAllCovered(UnwindingTree.toVertex(v));
        }
    }



    public synchronized void removeAllCovered(final Vertex v) {
        if (this.covered.containsKey(v)) {
            for (final Vertex u : this.covered.get(v)) {
                this.covererMap.remove(u);
            }

            this.covered.remove(v);
        }
    }

    /**
     * @param v
     * @param validateMaybe
     * @param aborter
     * @param checkInf
     * @return
     */
    public boolean refine(
        final Vertex v,
        final Abortion aborter,
        final boolean checkInf)
    {
        final List<Node<VertexID>> ancestors = this.getAncestorsInclusive(v);
        List<LinearDisjunction> interpolant = null;

        List<Edge<LinearConstraintsSystem, VertexID>> depTrans = null;
        final List<Edge<LinearConstraintsSystem, VertexID>> path = this.getEdgesPathFromRoot(v);

        List<LinearConstraintsSystem> depCond = new ArrayList<>();

        depTrans = this.getEdgesPathFromRoot(v); // this.getDependingTransitions(this.getInEdge(w));
        depCond = new ArrayList<>();

        for (final Edge<LinearConstraintsSystem, VertexID> t : depTrans) {
            depCond.add(t.getObject());
        }

        interpolant =
            this.solver.solve(
                ImmutableCreator.create(depCond));

        if (interpolant == null) {
            return false;
        }

        //final InterpolationTree iTree = InterpolationTree.tryCreate(depCond, aborter);

        //Log.report("ITREE", iTree.toTikZ());

        final List<LinearDisjunction> renamedInter = new ArrayList<>();
        for (final LinearDisjunction item : interpolant) {
            renamedInter.add(Vertex.removeInstanceTag(item));
            //            renamedInter
            //            .add(LinearDisjunction.create(item.rename(Vertex.getVariablesOriginalNames(item.getVariables()))));
        }

        for (int index = 0, i = 0; i < path.size(); i++) {

            final Edge<LinearConstraintsSystem, VertexID> t = path.get(i);

            if (depTrans.contains(t)) {
                index++;
            }

            final Vertex vertex = UnwindingTree.toVertex(t.getEndNode());

            final LinearDisjunction f = renamedInter.get(index);

            if (!this.solver.isImplied(vertex.getLabeling(), f)) {
                vertex.strengthenLabeling(this.solver.getDisjunctionSolver(), f);
                this.removeAllCovered(vertex);
                this.removeDescendantsAllCovered(vertex);

                if (vertex.isFalseLabel()) {
                    for (final Node<VertexID> d : this.getDescendants(vertex)) {
                        if (this.getAncestorsInclusive(v).contains(d)) {
                            continue;
                        }
                        UnwindingTree.toVertex(d).setInfeasible(); //.strengthenLabeling(this.termSolver, PolyConstraintsSystem.FALSE);
                        this.removeAllCovered(UnwindingTree.toVertex(d));
                    }
                }
            }
        }
        return true;
    }


    /**
     * @param father father vertex
     * @param uEdge creating edge from the unwinding graph
     * @return created child vertex
     */
    public Vertex addChild(final Vertex father, final Edge<LinearTransitionPair, LocationID> uEdge) {
        LinearTransitionPair tp = uEdge.getObject();

        final List<Pair<String, SimplePolynomial>> transitions = new ArrayList<>();
        transitions.addAll(tp.y.getTransitions());

        final Location fatherLocation = father.getLocation();

        if (fatherLocation instanceof PopLocation) {
            final SimplePolynomial val = father.getStackTop();
            final String var = ((PopLocation) fatherLocation).getVariable();

            transitions.add(new Pair<>(var, val));
        }

        tp = new LinearTransitionPair(tp.x, PolyRelation.createRelation(transitions));
        tp = tp.addSuffix(father.getStackSuffix());
        final Vertex child = father.createChild(this.getNextVertexId(), uEdge, tp);

        final PolyConstraintsSystem transitionCond = tp.x.rename(father.getInstances());
        final PolyConstraintsSystem condition = transitionCond.merge(child.getAssumption());

        if (condition.isFalse()) {
            child.setInfeasible();
        }

        Edge<LinearConstraintsSystem, VertexID> edge = null;

        edge =
            new Edge<>(
                father,
                child,
                LinearConstraintsSystem.create(condition));


            assert this.addEdge(edge);
            this.addLocationVertex(child);

            return child;
    }

    public boolean forceClose(final Vertex v, final Abortion aborter) {

        assert (!this.isCovered(v));
        if (!v.isCoverCandidate()) {
            return false;
        }

        if (this.isRoot(v)) { // || this.getInEdge(v).getObject().isTrue()) {
            return false;
        }

        final List<Vertex> vertices = this.getCoverCandidates(v);


        final HashSet<PolyDisjunction> labels = new HashSet<>();
        int attempts = 2; //1 + vertices.size() / 2;

        for (final Vertex w : vertices) {

            if (attempts == 0) {
                return false;
            }

            if (labels.contains(w.getLabeling())) {
                continue;
            }
            attempts--;
            if (this.forceCover(v, w, aborter)) {
                return true;
            }

        }
        return false;
    }

    protected boolean forceCover(final Vertex v, final Vertex w, final Abortion aborter) {
        final Vertex x = UnwindingTree.toVertex(this.nearestCommonAncestor(v, w));

        final LinearDisjunction fx = x.getLabeling();
        final LinearDisjunction fw = w.getLabeling();

        final LinearDisjunction disjFx = (Vertex.removeFullTag(fx));
        final LinearDisjunction disjFw = (Vertex.removeFullTag(fw));

        final List<Node<VertexID>> ancestors = this.getAncestorsInclusive(v);
        final int posX = ancestors.indexOf(x);
        final ArrayList<Node<VertexID>> path = new ArrayList<>(ancestors.subList(posX, ancestors.size()));

        final Vertex originalFather = UnwindingTree.toVertex(this.getFather(x));

        if (originalFather != null && originalFather.getLocation() instanceof ReturnLocation) {
            return false;
        }

        for (final LinearConstraintsSystem cSys : disjFx.getLinearConstraintsSystems()) {

            final List<Edge<PolyConstraintsSystem, VertexID>> tranitions = new ArrayList<>();
            final HashSet<Vertex> vertices = new HashSet<>();

            int maxId = -1;

            final UnwindingTree miniTree =
                UnwindingTree.create(new Location(-1), this.ug, originalFather, this.solver, aborter);
            Vertex curr = UnwindingTree.toVertex(miniTree.getRoot());


            final List<Vertex> newPath = new ArrayList<>();

            newPath.add(curr);

            for (int i = 0; i < path.size(); i++) {
                Edge<LinearTransitionPair, LocationID> t = null;
                if (i == 0) {
                    t =
                        new Edge<>(curr.getLocation(), UnwindingTree.toVertex(path.get(i)).getLocation(), new LinearTransitionPair(
                            cSys));


                } else {
                    t = UnwindingTree.toVertex(path.get(i)).getProgramEdge();
                }

                t.getObject();

                curr = miniTree.addChild(curr, t);

                newPath.add(curr);
            }

            maxId = path.isEmpty() ? -1 : path.get(path.size() - 1).getObject().getId() + 9999999;


            for (final LinearConstraintsSystem c : disjFw.negate().getLinearConstraintsSystems()) {
                final Vertex tail =
                    miniTree.addChild(curr, new Edge<>(
                        curr.getLocation(),
                        new Location(maxId++),
                        new LinearTransitionPair(c)));

                newPath.add(tail);

                final boolean refined = miniTree.refine(tail, aborter, true);

                if (refined) {
                    for (int i = 0; i < path.size(); i++) {

                        final Vertex vertex = (Vertex) path.get(i);
                        final LinearDisjunction f = newPath.get(i + 1).getLabeling();

                        if (!this.solver.isImplied(vertex.getLabeling(), f)) {

                            this.removeAllCovered(vertex);
                            this.removeDescendantsAllCovered(vertex);

                            vertex.strengthenLabeling(this.solver.getDisjunctionSolver(), f);

                            if (vertex.isFalseLabel()) {
                                for (final Node<VertexID> d : this.getDescendants(vertex)) {
                                    if (this.getAncestorsInclusive(v).contains(d)) {
                                        continue;
                                    }
                                    UnwindingTree.toVertex(d).setInfeasible();
                                    this.removeAllCovered(UnwindingTree.toVertex(d));
                                }
                            }
                        }

                    }
                } else {
                    return false;
                }
            }
        }
        this.addCovered(v, w);



        return true;



    }

    @Override
    public boolean removeNode(final Node<VertexID> v) {
        this.removeAllCovered((Vertex) v);

        for (final Node<VertexID> c : new HashSet<>(this.getOut(v))) {
            this.removeNode(c);
        }

        assert super.removeNode(v);

        return true;
    }

    private boolean tryCover(final Vertex v, final Vertex w, final Abortion aborter) {
        assert (!this.isCovered(v));
        if (!this.solver.isImplied(v.getLabeling(), w.getLabeling())) {
            return false;
        }

        this.addCovered(v, w);
        this.removeDescendantsAllCovered(v);
        return true;
    }

    /**
     * @param v - vertex
     */
    public boolean close(final Vertex v, final Abortion aborter) {
        for (final Vertex w : this.getCoverCandidates(v)) {
            if (this.tryCover(v, w, aborter)) {
                return true;
            }
        }
        return false;
    }



    private final HashMap<Triple<Location, Integer, SimplePolynomial>, ArrayList<Vertex>> LOCATION_VERTICES =
        new HashMap<>();


        private void addLocationVertex(final Vertex node) {
            final Vertex vertex = node;
            final Triple<Location, Integer, SimplePolynomial> p =
                new Triple<>(vertex.getLocation(), vertex.getStackDepthLabel(), vertex.getStackTop());

                synchronized (this.LOCATION_VERTICES) {
                    if (!this.LOCATION_VERTICES.containsKey(p)) {
                        this.LOCATION_VERTICES.put(p, new ArrayList<Vertex>());
                    }
                    this.LOCATION_VERTICES.get(p).add(node);
                }
        }

        public ArrayList<Vertex> getCoverCandidates(final Vertex node) {
            final ArrayList<Vertex> list = new ArrayList<>();
            final Triple<Location, Integer, SimplePolynomial> pLoc =
                new Triple<>(node.getLocation(), node.getStackDepthLabel(), node.getStackTop());


                for (final Vertex u : this.LOCATION_VERTICES.get(pLoc)) {
                    if (u.equals(node)) {
                        Collections.reverse(list);
                        return list;
                    }

                    if (this.contains(u) && !this.isCovered(u)) {
                        list.add(u);
                    }
                }

                throw new RuntimeException("Vertex Exception");
        }

        public boolean refinePathTo(
            final Vertex v,
            final Abortion aborter,
            final boolean checkInf)
        {


            if (!this.refine(v, aborter, checkInf)) {
                return false;
            }
            for (final Node<VertexID> w : this.getAncestors(v)) {
                if (this.close(UnwindingTree.toVertex(w), aborter)) {
                    break;
                }
            }

            return true;
        }

        /**
         * @return an uncovered leaves, if such exists. Otherwise, null
         */
        public Vertex getUncoveredLeaf() {

            final ArrayList<Node<VertexID>> l = new ArrayList<>(this.getLeaves());
            Collections.reverse(l);
            for (final Node<VertexID> n : l) {
                final Vertex v = UnwindingTree.toVertex(n);
                if (!v.isFalseLabel() && !this.isCovered(v)) {
                    return v;
                }
            }
            return null;
        }

        /**
         * @param v the vertex being covered
         * @param w the covering vertex
         */
        private synchronized void addCovered(final Vertex v, final Vertex w) {
            assert !this.isCovered(v);

            this.covererMap.put(v, w);

            if (!this.covered.containsKey(w)) {
                this.covered.put(w, new HashSet<Vertex>());
            }

            this.covered.get(w).add(v);
        }

        public InterpolationSolver getInterpolationSolver() {
            return this.solver;
        }

        private void compress(final Vertex node, final SimpleTree<VertexID, LinearConstraintsSystem> resTree) {
            final Set<SimplePolyConstraint> constraints = new HashSet<>();

            Vertex curr = node;

            while (this.getOut(curr).size() == 1) {
                final Edge<LinearConstraintsSystem, VertexID> edge = this.getOutEdges(curr).iterator().next();
                constraints.addAll(edge.getObject().getConstraints());
                curr = (Vertex) edge.getEndNode();
            }

            if (!curr.equals(node)) {
                resTree.addEdge(node, curr, LinearConstraintsSystem.create(constraints));
            }

            for (final Edge<LinearConstraintsSystem, VertexID> edge : this.getOutEdges(curr)) {
                if (ToolBox.buildFalse().equals(edge.getObject())) {
                    continue;
                }

                resTree.addEdge(edge);
                this.compress((Vertex) edge.getEndNode(), resTree);
            }
        }


}
