package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph;

import java.util.*;

import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.TermTransitionPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.SAT.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Graph representing a program, relations and constraints are represented by terms
 * @author marinag
 */
public class ProgramGraph extends SimpleGraph<LocationID, TermTransitionPairsSet> {

    /**
     *
     */
    private static final long serialVersionUID = 6715350186051334662L;

    /**
     * Start location (root)
     */
    private Location root;

    protected void setStarLocation(final Location root) {
        this.root = root;

    }

    /**
     * Creates a graph with a single location as its start location (root)
     * @param root start location
     */
    public ProgramGraph(final Location root) {
        this.root = root;
    }

    /**
     * Creates a program graph according to the given parameters
     * @param root start location
     * @param transitions edges
     * @param locations locations
     */
    public ProgramGraph(
        final Location root,
        final Set<Edge<TermTransitionPairsSet, LocationID>> transitions,
        final Set<Node<LocationID>> locations)
    {
        super(locations, transitions);
        this.root = root;
    }


    /**
     * Creates an un-rooted program graph corresponding to the given simple graph
     * @param graph SimpleGraph
     */
    public ProgramGraph(final SimpleGraph<LocationID, TermTransitionPairsSet> graph) {
        super(graph.getNodes(), graph.getEdges());
        this.root = null;
    }

    /**
     * Creates an simple un-rooted program graph
     */
    public ProgramGraph() {
        super();
        this.root = null;

    }

    /**
     * Creates a program graph according to the given parameters
     * @param start start location
     * @param edges set of edges
     */
    public ProgramGraph(final Location start, final Set<Edge<TermTransitionPairsSet, LocationID>> edges) {
        super(new HashSet<Node<LocationID>>(), edges);
        this.root = start;
    }

    /**
     * Sub-method of createOrder()
     */
    private
    int
    createOrder(final Node<LocationID> node, final int order, final Map<Node<LocationID>, Integer> orderMap)
    {
        if (orderMap.containsKey(node)) {
            return order;
        }

        orderMap.put(node, order);

        int newOrder = order + 1;

        if (this.contains(node)) {

            for (final Node<LocationID> e : this.getOut(node)) {
                newOrder = this.createOrder(e, newOrder, orderMap);
            }
        }

        return newOrder;
    }

    /**
     * @return DFS order over the nodes, starting from the starting location. In case of a not specified starting location returns and empty map
     */
    public Map<Node<LocationID>, Integer> createOrder() {

        final Map<Node<LocationID>, Integer> orderMap = new HashMap<>();

        if (this.getStartLocation() != null) {
            this.createOrder(this.getStartLocation(), 0, orderMap);
        }

        return orderMap;
    }

    /**
     * @param locations set of graph locations
     * @return a map of cut point locations to a set of names of variable that are altered at the cycles of the given cut point
     */
    public List<Location> getCutPoints() {
        final Map<Node<LocationID>, Integer> order = this.createOrder();

        final Set<Location> cutPoints = new HashSet<>();
        for (final Node<LocationID> node : this.getNodes()) {
            if (!order.containsKey(node)) {
                continue;
            }

            final Location loc = (Location) node;

            for (final Node<LocationID> l : this.getOut(loc)) {
                final int orderA = order.get(loc);
                final int orderB = order.get(l);

                if (orderA >= orderB) {
                    cutPoints.add((Location) l);
                }
            }
        }

        final List<Location> result = new ArrayList<>();

        for (final Location l : cutPoints) {

            int i = 0;
            while (i < result.size() && order.get(result.get(i)) > order.get(l)) {
                i++;
            }
            result.add(i, l);
        }

        for (final Location l : new ArrayList<>(result)) {
            if (this.getEdge(l, l) != null && this.getOut(l).size() == 1) {
                while (result.remove(l)) {
                    ;
                }
                result.add(l);
            }
        }

        return result;
    }


    /**
     * @param l program location
     * @return true in case this graph is rooted and l is reached from the the root, otherwise return false
     */
    public boolean isReachable(final Location l) {
        if (!this.contains(l)) {
            return false;
        }

        if (this.root == null) {
            return true;
        }

        return this.hasPath(this.root, l);
    }


    /**
     * @param start start location
     * @param end end location
     * @return set of all locations between start and end
     */
    private Set<Location> getLocationsBetween(final Location start, final Location end) {
        return this.getLocationsBetween(start, end, new HashSet<Location>(), end);
    }

    /**
     * @param start start location
     * @param end end location
     * @param found set of location found till now
     * @param curr current location
     * @return set of all locations between start and end
     */
    private Set<Location> getLocationsBetween(
        final Location start,
        final Location end,
        final HashSet<Location> found,
        final Location curr)
        {
        final HashSet<Location> result = new HashSet<>();

        if (found.contains(curr)) {
            return result;
        }

        if (end.equals(curr)) {
            return found;
        }

        found.add(curr);

        for (final Edge<TermTransitionPairsSet, LocationID> t : this.getOutEdges(curr)) {
            result.addAll(this.getLocationsBetween(start, end, found, (Location) (t.getEndNode())));
        }

        return result;
        }


    /**
     * @return start location
     */
    public Location getStartLocation() {
        return this.root;
    }

    @Override
    public ProgramGraph getSubGraph(final Set<Node<LocationID>> nodes) {
        return new ProgramGraph(super.getSubGraph(nodes));
    }


    /**
     * @return the reachable sub graph from the root. in case of an un-rooted graph, returns an empty graph
     */
    public ProgramGraph determineReachable() {
        if (this.root == null) {
            return new ProgramGraph();
        }

        final Set<Node<LocationID>> rNodes = this.determineReachableNodes(Arrays.asList((Node<LocationID>) this.root));
        final Set<Edge<TermTransitionPairsSet, LocationID>> rEdges = this.getSubGraph(rNodes).getEdges();
        return new ProgramGraph(this.root, rEdges);
    }

    @Override
    public String toString() {
        final StringBuilder builder = new StringBuilder();

        builder.append("ProgramGraph\n");

        if (this.root != null) {
            builder.append("Start: " + this.root.toString() + "\n");
        }

        builder.append("\nEdges:\n");

        for (final Edge<TermTransitionPairsSet, LocationID> edge : this.getEdges()) {
            builder.append(edge.toString() + "\n");
        }

        return builder.toString();
    }


    /**
     * @param s PolyDisjunction edge
     * @return all possible PolyConstraintsSystem edges resulted from the given edge
     */
    public static
    List<Edge<TermTransitionPair, LocationID>>
    splitEdge(final Edge<TermTransitionPairsSet, LocationID> s)
    {
        final List<Edge<TermTransitionPair, LocationID>> edges = new ArrayList<>();

        for (final TermTransitionPair d : s.getObject().getTransitionsPairs()) {
            if (TermTools.isFalse(d.x)) {
                continue;
            }

            edges.add(new Edge<>(s.getStartNode(), s.getEndNode(), d));

        }
        return edges;
    }

    public static List<Edge<TermTransitionPair, LocationID>> splitEdges(
        final Set<Edge<TermTransitionPairsSet, LocationID>> edges)
        {
        final List<Edge<TermTransitionPair, LocationID>> result = new ArrayList();

        for (final Edge<TermTransitionPairsSet, LocationID> s : edges) {
            result.addAll(ProgramGraph.splitEdge(s));
        }

        return result;
        }
}