package aprove.verification.complexity.CpxIntTrsProblem.Structures;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Wraps the mutable {@link Graph} class to be logical immutable.
 */
public class CpxIntGraph implements Immutable {
    public enum RemovalTests {
        RootSymbolTest {
            @Override
            public boolean connects(CpxIntTupleRule from, CpxIntTupleRule to, Abortion abortion) {
                FunctionSymbol toSym = to.getRootSymbol();
                for (TRSFunctionApplication r : from.getRights()) {
                    if (toSym.equals(r.getRootSymbol())) {
                        return true;
                    }
                }
                return false;
            }
        },
        SMTUnsatTest {
            @Override
            public boolean connects(CpxIntTupleRule from, CpxIntTupleRule to, Abortion abortion)
                throws AbortionException
            {
                FunctionSymbol toSym = to.getRootSymbol();
                for (int i = 0, l = from.getRights().size(); i < l; ++i) {
                    TRSFunctionApplication r = from.getRights().get(i);
                    if (!toSym.equals(r.getRootSymbol())) {
                        continue;
                    }
                    CpxIntTupleRule chained = from.chainWithRule(to, i);
                    ConstraintInformation info = chained.getConstraintInformation();
                    if (!info.isUnsatisfiable(abortion)) {
                        return true;
                    }
                    ++i;
                }
                return false;
            }
        };

        public abstract boolean connects(CpxIntTupleRule from, CpxIntTupleRule to, Abortion abortion)
            throws AbortionException;
    }

    static private final ImmutableLinkedHashSet<RemovalTests> defaultTests;
    static {
        LinkedHashSet<RemovalTests> rawtests = new LinkedHashSet<>();
        rawtests.add(RemovalTests.RootSymbolTest);
        rawtests.add(RemovalTests.SMTUnsatTest);
        defaultTests = ImmutableCreator.create(rawtests);
    }

    /** Each edge stores the unsuccessful tests that were done to remove it. */
    private final Graph<CpxIntTupleRule, Set<RemovalTests>> graph;

    private CpxIntGraph(Graph<CpxIntTupleRule, Set<RemovalTests>> graph) {
        this.graph = graph;
    }

    public static void updateConnection(
        Graph<CpxIntTupleRule, Set<RemovalTests>> graph,
        Node<CpxIntTupleRule> from,
        Node<CpxIntTupleRule> to,
        LinkedHashSet<RemovalTests> tests,
        boolean useCache,
        Abortion abortion) throws AbortionException
    {
        Set<RemovalTests> finishedTests = new LinkedHashSet<>();
        if (useCache) {
            if (graph.contains(from, to)) {
                finishedTests.addAll(graph.getEdgeObject(from, to));
            } else {
                return;
            }
        }

        for (RemovalTests test : tests) {
            if (finishedTests.contains(test)) {
                continue;
            }
            if (test.connects(from.getObject(), to.getObject(), abortion)) {
                finishedTests.add(test);
            } else {
                graph.removeEdge(from, to);
                return;
            }
        }
        graph.addEdge(from, to, finishedTests);
    }

    public static CpxIntGraph createDefaultApproximation(Set<CpxIntTupleRule> rules, Abortion abortion)
        throws AbortionException
    {
        Graph<CpxIntTupleRule, Set<RemovalTests>> graph = new Graph<>();
        Set<Node<CpxIntTupleRule>> nodes = new LinkedHashSet<>();
        for (CpxIntTupleRule rule : rules) {
            Node<CpxIntTupleRule> node = new Node<>(rule);
            nodes.add(node);
            graph.addNode(node);
        }
        for (Node<CpxIntTupleRule> from : nodes) {
            for (Node<CpxIntTupleRule> to : nodes) {
                CpxIntGraph.updateConnection(graph, from, to, CpxIntGraph.defaultTests, false, abortion);
            }
        }
        return new CpxIntGraph(graph);
    }

    public Set<CpxIntTupleRule> pre(CpxIntTupleRule rule) {
        Node<CpxIntTupleRule> node = this.graph.getNodeFromObject(rule);
        Set<Node<CpxIntTupleRule>> in = this.graph.getIn(node);
        Set<CpxIntTupleRule> rv = new LinkedHashSet<>();
        for (Node<CpxIntTupleRule> n : in) {
            rv.add(n.getObject());
        }
        return rv;
    }

    private void ruleToDot(
        StringBuilder t,
        CpxIntTupleRule rule,
        boolean isStartRule,
        ImmutableLinkedHashMap<CpxIntTupleRule, ComplexityValue> k,
        Map<CallArgument, LocalComplexityValue> bounds)
    {
        HTML_Util hu = new HTML_Util();
        t.append(" [");
        t.append("label=<");
        t.append(rule.export(hu));
        t.append("<br/>(");
        boolean first = true;
        for (CallArgument alpha : rule.getCallArguments()) {
            if (first) {
                first = false;
            } else {
                t.append(",");
            }
            LocalComplexityValue b = bounds.get(alpha);
            t.append(b.export(hu));
        }
        t.append(")");
        if (!k.get(rule).isInfinite()) {
            t.append("<br/>");
            ComplexityValue complexity = k.get(rule);
            t.append(complexity);
        }
        t.append(">");
        if (!k.get(rule).isInfinite()) {
            t.append(", color=\"gray\", fillcolor=\"lightgray\", style=\"filled\", fontcolor=\"gray\"");
        }
        t.append(", shape=\"" + (isStartRule ? "octagon" : "box") + "\"");
        t.append("];");
    }

    private void toDot(
        StringBuilder t,
        ImmutableLinkedHashMap<CpxIntTupleRule, ComplexityValue> k,
        Map<CallArgument, LocalComplexityValue> bounds,
        ImmutableLinkedHashSet<FunctionSymbol> startSymbols)
    {
        t.append("digraph dp_graph {\n");
        t.append("subgraph cluster_key { style=filled; color=lightgrey; node [style=filled,color=white];"
            + "start [label=\"start node\", shape=octagon]; normal [label=\"normal node\", shape=box]; }");
        for (Node<CpxIntTupleRule> from : this.graph.getNodes()) {
            Set<Node<CpxIntTupleRule>> out = this.graph.getOut(from);
            if (out == null) {
                out = new LinkedHashSet<>();
            }
            t.append(from.getNodeNumber());
            CpxIntTupleRule rule = from.getObject();
            boolean isStartRule = startSymbols.contains(rule.getRootSymbol());
            this.ruleToDot(t, rule, isStartRule, k, bounds);
            if (out.isEmpty()) {
                continue;
            }
            t.append(from.getNodeNumber() + " -> {");
            for (Node<CpxIntTupleRule> to : out) {
                t.append(to.getNodeNumber() + " ");
            }
            t.append("};\n");
        }
        t.append("}\n");
    }

    public String export(
        Export_Util eu,
        ImmutableLinkedHashMap<CpxIntTupleRule, ComplexityValue> k,
        Map<CallArgument, LocalComplexityValue> bounds,
        ImmutableLinkedHashSet<FunctionSymbol> startSymbols)
    {
        if (eu instanceof HTML_Util) {
            StringBuilder sb = new StringBuilder();
            this.toDot(sb, k, bounds, startSymbols);
            return "<textarea>" + eu.escape(sb.toString()) + "</textarea>";
        }
        return "";
    }

    public Set<CpxIntTupleRule> getRulesReaching(Iterable<CpxIntTupleRule> s) {
        ArrayStack<Node<CpxIntTupleRule>> todo = new ArrayStack<>();
        HashSet<Node<CpxIntTupleRule>> visited = new HashSet<>();
        LinkedHashSet<CpxIntTupleRule> result = new LinkedHashSet<>();

        for (CpxIntTupleRule r : s) {
            Node<CpxIntTupleRule> node = this.graph.getNodeFromObject(r);
            todo.push(node);
        }

        while (!todo.isEmpty()) {
            Node<CpxIntTupleRule> node = todo.pop();
            if (visited.contains(node)) {
                continue;
            }
            visited.add(node);
            CpxIntTupleRule rule = node.getObject();
            result.add(rule);

            for (Node<CpxIntTupleRule> inNode : this.graph.getIn(node)) {
                todo.push(inNode);
            }
        }

        return result;
    }

    public CpxIntGraph createByRemovingRules(Set<CpxIntTupleRule> removed) {
        LinkedHashSet<Node<CpxIntTupleRule>> keptNodes = new LinkedHashSet<>();
        for (Node<CpxIntTupleRule> node : this.graph.getNodes()) {
            if (!removed.contains(node.getObject())) {
                keptNodes.add(node);
            }
        }
        return new CpxIntGraph(this.graph.getSubGraph(keptNodes));
    }

    public Set<CpxIntTupleRule> getRules() {
        Set<CpxIntTupleRule> nodes = new LinkedHashSet<>();
        for (Node<CpxIntTupleRule> node : this.graph.getNodes()) {
            nodes.add(node.getObject());
        }
        return nodes;
    }

    public Set<CpxIntTupleRule> getOut(CpxIntTupleRule rule) {
        Node<CpxIntTupleRule> node = this.graph.getNodeFromObject(rule);
        Set<CpxIntTupleRule> out = new LinkedHashSet<>();
        for (Node<CpxIntTupleRule> n : this.graph.getOut(node)) {
            out.add(n.getObject());
        }
        return out;
    }

    public
        CpxIntGraph
        createByReplacingRules(Map<CpxIntTupleRule, Set<CpxIntTupleRule>> replacements, Abortion abortion)
            throws AbortionException
    {
        Graph<CpxIntTupleRule, Set<RemovalTests>> g = this.graph.getCopy();

        // Replacing one rule after another might lead to different results than replacing them all at once,
        // if the domain and range of replacements intersect.
        // But this will only occur in obscure cases that are not triggered by the corresponding processors.
        // Still, one should be aware of it.
        for (Entry<CpxIntTupleRule, Set<CpxIntTupleRule>> e : replacements.entrySet()) {
            CpxIntTupleRule removedRule = e.getKey();
            Set<CpxIntTupleRule> addedRules = e.getValue();

            Node<CpxIntTupleRule> fromNode = g.getNodeFromObject(removedRule);

            Set<Node<CpxIntTupleRule>> toNodes = new LinkedHashSet<>();
            for (CpxIntTupleRule toRule : addedRules) {
                Node<CpxIntTupleRule> toNode = g.getNodeFromObject(toRule);
                if (toNode == null) {
                    toNode = new Node<>(toRule);
                    g.addNode(toNode);
                }
                toNodes.add(toNode);
            }

            g.removeNode(fromNode);

            // repair all edges
            for (Node<CpxIntTupleRule> node : g.getNodes()) {
                for (Node<CpxIntTupleRule> newNode : toNodes) {
                    CpxIntGraph.updateConnection(g, node, newNode, CpxIntGraph.defaultTests, false, abortion);
                    CpxIntGraph.updateConnection(g, newNode, node, CpxIntGraph.defaultTests, false, abortion);
                }
            }
        }

        return new CpxIntGraph(g);
    }

    public Map<CpxIntTupleRule, Set<CpxIntTupleRule>> getNodesWithOutEdges() {
        Map<CpxIntTupleRule, Set<CpxIntTupleRule>> rv = new LinkedHashMap<>();

        for (Node<CpxIntTupleRule> node : this.graph.getNodes()) {
            LinkedHashSet<CpxIntTupleRule> rules = new LinkedHashSet<>();
            for (Node<CpxIntTupleRule> outNode : this.graph.getOut(node)) {
                rules.add(outNode.getObject());
            }
            rv.put(node.getObject(), rules);
        }

        return rv;
    }

    public Set<CpxIntTupleRule> getOut(CpxIntTupleRule rule, int i) {
        Set<CpxIntTupleRule> out = this.getOut(rule);
        // approximate, as long as the graph doesn't support edges from specific arguments of RHSs
        FunctionSymbol fs = rule.getRights().get(i).getRootSymbol();
        for (Iterator<CpxIntTupleRule> it = out.iterator(); it.hasNext();) {
            CpxIntTupleRule outRule = it.next();
            if (!fs.equals(outRule.getLeft().getRootSymbol())) {
                it.remove();
            }
        }
        return out;
    }

    public Set<Pair<CpxIntTupleRule, Integer>> getIn(CpxIntTupleRule rule) {
        Set<Node<CpxIntTupleRule>> in = this.graph.getIn(this.graph.getNodeFromObject(rule));
        Set<Pair<CpxIntTupleRule, Integer>> rv = new LinkedHashSet<>();
        FunctionSymbol fs = rule.getRootSymbol();

        for (Node<CpxIntTupleRule> e : in) {
            CpxIntTupleRule inRule = e.getObject();
            ImmutableList<TRSFunctionApplication> rhss = inRule.getRights();
            int l = rhss.size();
            for (int i = 0; i < l; ++i) {
                if (fs.equals(rhss.get(i).getRootSymbol())) {
                    rv.add(new Pair<>(inRule, i));
                }
            }
        }

        return rv;
    }

    public Set<CpxIntTupleRule> getRulesReachableFrom(LinkedHashSet<CpxIntTupleRule> startRules) {
        ArrayStack<Node<CpxIntTupleRule>> todo = new ArrayStack<>();
        HashSet<Node<CpxIntTupleRule>> visited = new HashSet<>();
        LinkedHashSet<CpxIntTupleRule> result = new LinkedHashSet<>();

        for (CpxIntTupleRule r : startRules) {
            Node<CpxIntTupleRule> node = this.graph.getNodeFromObject(r);
            todo.push(node);
        }

        while (!todo.isEmpty()) {
            Node<CpxIntTupleRule> node = todo.pop();
            if (visited.contains(node)) {
                continue;
            }
            visited.add(node);
            CpxIntTupleRule rule = node.getObject();
            result.add(rule);

            for (Node<CpxIntTupleRule> inNode : this.graph.getOut(node)) {
                todo.push(inNode);
            }
        }

        return result;

    }
}
