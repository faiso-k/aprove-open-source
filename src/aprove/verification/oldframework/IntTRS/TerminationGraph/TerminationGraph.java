package aprove.verification.oldframework.IntTRS.TerminationGraph;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.runtime.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.TerminationGraph.IntTRSTerminationGraphProcessor.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Represents a graph, whose nodes are rule. Here two rules are connected, when
 * it may be possible to use these rules one after another. This class can also
 * simplify the SCCs.
 * @author Matthias Hoelzel
 */
public final class TerminationGraph {
    /** Set of nodes. */
    private final Set<IGeneralizedRule> nodes;

    /** Set of edges. */
    private final LinkedHashMap<IGeneralizedRule, LinkedHashSet<IGeneralizedRule>> edges;

    /** Set of inverted edges. */
    private final LinkedHashMap<IGeneralizedRule, LinkedHashSet<IGeneralizedRule>> invertedEdges;

    /** Non-trivial SCCs */
    private LinkedList<Set<IGeneralizedRule>> nonTrivialSccs;

    /** SCCs */
    private LinkedList<Set<IGeneralizedRule>> sccs;

    /** The proof */
    private final IntTRSTerminationGraphProof proof;

    /** Name generator. */
    private final FreshNameGenerator ng;

    /** Aborter */
    private final Abortion aborter;

    /**
     * Creates an empty KITTeLGraph.
     * @param ruleSet set of KITTeLRules
     * @param gen name generator
     * @param kittelProof some proof
     */
    private TerminationGraph(
        final Set<IGeneralizedRule> ruleSet,
        final FreshNameGenerator gen,
        final Abortion abortion,
        final IntTRSTerminationGraphProof kittelProof)
    {
        this.ng = gen;
        this.aborter = abortion;
        this.nodes = ruleSet;
        this.edges = new LinkedHashMap<>(this.nodes.size());
        this.proof = kittelProof;
        this.invertedEdges = new LinkedHashMap<>(this.nodes.size());
        for (final IGeneralizedRule iRule : ruleSet) {
            this.edges.put(iRule, new LinkedHashSet<IGeneralizedRule>(this.nodes.size()));
            this.invertedEdges.put(iRule, new LinkedHashSet<IGeneralizedRule>(this.nodes.size()));
        }
    }

    /**
     * Connects two rule. Please note, that this will change the graph.
     * @param from IGeneralizedRule
     * @param to IGeneralizedRule
     */
    public void connect(final IGeneralizedRule from, final IGeneralizedRule to) {
        this.edges.get(from).add(to);
        this.invertedEdges.get(to).add(from);
        this.sccs = null;
    }

    /**
     * Disconnects two rules. Please note, that this will change the graph.
     * @param from IGeneralizedRule
     * @param to IGeneralizedRule
     */
    public void disconnect(final IGeneralizedRule from, final IGeneralizedRule to) {
        this.edges.get(from).remove(to);
        this.invertedEdges.get(to).remove(from);
        this.sccs = null;
    }

    /**
     * Builds a KITTeLGraph.
     * @param ruleSet set of rules
     * @param startTerm some start term
     * @param factory formula factory
     * @param aborter some aborter
     * @param ng name generator
     * @param kittelProof some proof
     * @return KITTeLGraph
     * @throws AbortionException can be aborted
     */
    public static TerminationGraph buildGraph(
        final Set<IGeneralizedRule> ruleSet,
        final TRSFunctionApplication startTerm,
        final FormulaFactory<SMTLIBTheoryAtom> factory,
        final Abortion aborter,
        final FreshNameGenerator ng,
        final IntTRSTerminationGraphProof kittelProof) throws AbortionException
    {
        final TerminationGraph graph = new TerminationGraph(ruleSet, ng, aborter, kittelProof);

        // Try to turn every pair of rule into an edge:
        for (final IGeneralizedRule from : ruleSet) {
            aborter.checkAbortion();
            for (final IGeneralizedRule iRule : ruleSet) {
                if (!Options.certifier.isNone()) {
                    // certified mode only looks at root symbols
                    TRSTerm t = from.getRight();
                    if (t.isVariable() || ((TRSFunctionApplication) t).getFunctionSymbol().equals(iRule.getRootSymbol()))
                        graph.connect(from, iRule);
                    continue;                
                }
                final IGeneralizedRule to = from != iRule ? iRule : ToolBox.renameVariablesInRule(iRule, ng);
                final TRSSubstitution unifier = to.getLeft().getMGU(from.getRight());

                // There will be only a edge, when they unify:
                if (unifier != null) {
                    final TRSTerm fromCondition = from.getCondTerm();
                    final TRSTerm toCondition = to.getCondTerm();

                    final LinkedList<Formula<SMTLIBTheoryAtom>> formulas = new LinkedList<>();

                    // Test whether it is possible, to use these rules in a chain:
                    ToolBox.boolTermToSMTTheoryAtoms(fromCondition, ng, formulas, factory, aborter);
                    aborter.checkAbortion();
                    ToolBox.boolTermToSMTTheoryAtoms(
                            toCondition.applySubstitution(unifier),
                            ng,
                            formulas,
                            factory,
                            aborter);

                    YNM answer;
                    try {
                        answer = ToolBox.SMT_ENGINE.satisfiable(formulas, SMTLogic.QF_LIA, aborter);
                    } catch (final WrongLogicException e) {
                        System.err.println("Solver error: " + e.getErrorMessage());
                        answer = YNM.MAYBE;
                    }
                    if (answer != YNM.NO) {
                        graph.connect(from, iRule);
                    }
                }
            }
        }

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger logger = DebugLogger.getLogger("graph");
            logger.logln(graph.toString());
        }

        if (startTerm != null) {
            return graph.getSubGraph(graph.getReachableNodes(startTerm.getRootSymbol()));
        } else {
            return graph;
        }
    }

    /**
     * Returns the set of rules reachable from the given symbol sym
     * @param sym some function symbol
     * @return a set of rules
     */
    public Set<IGeneralizedRule> getReachableNodes(final FunctionSymbol sym) {
        final LinkedHashSet<IGeneralizedRule> visited = new LinkedHashSet<>(this.nodes.size());

        for (final IGeneralizedRule startRule : this.nodes) {
            if (startRule.getLeft().getRootSymbol().equals(sym)) {
                TerminationGraph.dfs(startRule, this.edges, visited, null, null);
            }
        }

        return visited;
    }

    /**
     * Returns the nodes of the current graph.
     * @return set of rules
     */
    public ImmutableSet<IGeneralizedRule> getNodes() {
        return ImmutableCreator.create(this.nodes);
    }

    /**
     * Returns a set of nodes, reachable from the given rule via an edge.
     * @param from some rule
     * @return set of rules
     */
    public Set<IGeneralizedRule> getEdges(final IGeneralizedRule from) {
        return ImmutableCreator.create(this.edges.get(from));
    }

    /**
     * Returns a list of non-trivial strongly connected components.
     * @return List\<Set\<IGeneralizedRule\>\>
     */
    public List<Set<IGeneralizedRule>> getNTSCCs() {
        if (this.nonTrivialSccs == null) {
            this.calculateSCCs();
        }
        return this.nonTrivialSccs;
    }

    /**
     * Returns a list of strongly connected components. This does not throw away
     * trivial SCCs.
     * @return List\<Set\<IGeneralizedRule\>\>
     */
    public List<Set<IGeneralizedRule>> getSCCs() {
        if (this.sccs == null) {
            this.calculateSCCs();
        }
        return this.sccs;
    }

    /**
     * Returns a list of non-trivial strongly connected components, which are
     * simplified by using transformations.
     * @return List of sets of IGeneralizedRules
     * @throws AbortionException can be aborted
     */
    public List<Set<IGeneralizedRule>> getSimplifiedSCCs(
        final boolean useConstraintTransformation,
        final boolean defaultChainingOnly) throws AbortionException
    {
        final List<Set<IGeneralizedRule>> simplified = new LinkedList<>();
        final List<Set<IGeneralizedRule>> sccList = this.getNTSCCs();
        for (final Set<IGeneralizedRule> scc : sccList) {
            this.aborter.checkAbortion();
            final Set<IGeneralizedRule> transformedRules =
                this.applyTransformations(scc, useConstraintTransformation, defaultChainingOnly);
            final Set<IGeneralizedRule> simplifiedTransformedRules =
                RuleSimplification.simplifyRules(transformedRules, this.ng, this.aborter);
            simplified.add(simplifiedTransformedRules);
        }

        return simplified;
    }

    /**
     * Applies some transformations to "simplify" the intTRS.
     * @param scc set of rules to be transformed
     * @return result: set of rules
        * @throws AbortionException can be aborted
     */
    private Set<IGeneralizedRule> applyTransformations(
        final Set<IGeneralizedRule> scc,
        final boolean useConstraintTransformation,
        final boolean defaultChainingOnly) throws AbortionException
    {
        TerminationGraph subGraph = this.getSubGraph(scc);

        Set<IGeneralizedRule> newSCC = scc;
        if (useConstraintTransformation) {
            final LinkedHashMap<IGeneralizedRule, IGeneralizedRule> substitution = subGraph.addFurtherConstraints(scc);

            newSCC = TerminationGraph.mapSet(substitution, scc);
            subGraph = subGraph.mapGraph(substitution);
        }

        return subGraph.applyChaining(newSCC, defaultChainingOnly);
    }

    /**
     * Adds some more constraints and returns a mapping from the old rules to
     * the new one.
     * @param scc current scc
     * @return mapping from the old rules to the new rules
     * @throws AbortionException can be aborted
     */
    private LinkedHashMap<IGeneralizedRule, IGeneralizedRule> addFurtherConstraints(final Set<IGeneralizedRule> scc)
        throws AbortionException
    {
        final TerminationGraph subGraph = this.getSubGraph(scc);

        final LinkedHashMap<IGeneralizedRule, IGeneralizedRule> substitution = new LinkedHashMap<>();

        for (final Entry<IGeneralizedRule, LinkedHashSet<IGeneralizedRule>> e : subGraph.invertedEdges.entrySet()) {
            this.aborter.checkAbortion();
            final LinkedHashSet<IGeneralizedRule> predecessors = e.getValue();
            // If we have a rule, that has only one predecessor,
            // then we use this predecessor to generate some constraints
            // that can be added to the current rule:
            if (predecessors.size() == 1) {
                final IGeneralizedRule currentRule = e.getKey();

                // Get the renamed predecessor rule:
                final IGeneralizedRule predecessor = predecessors.iterator().next();

                final BackwardConstraintsInference bci =
                    new BackwardConstraintsInference(currentRule, predecessor, this.ng);
                final IGeneralizedRule newRule = bci.calculateResult();
                substitution.put(currentRule, newRule);
                this.proof.exportTransformation(currentRule, newRule);
            }
        }

        return substitution;
    }

    /**
     * Maps a whole set.
     * @param substitution mapping of rules to rules
     * @param toBeMapped set of rules
     * @return set of rules
     */
    private static LinkedHashSet<IGeneralizedRule> mapSet(
        final LinkedHashMap<IGeneralizedRule, IGeneralizedRule> substitution,
        final Set<IGeneralizedRule> toBeMapped)
    {
        final LinkedHashSet<IGeneralizedRule> result = new LinkedHashSet<>(toBeMapped.size());

        for (final IGeneralizedRule rule : toBeMapped) {
            IGeneralizedRule newRule = rule;
            if (substitution.containsKey(newRule)) {
                newRule = substitution.get(newRule);
            }
            assert newRule != null : "Malformed substitution: " + substitution;
            result.add(newRule);
        }

        return result;
    }

    /**
     * Applies an injective mapping from rules to rules to this graph and
     * returns a mapped version of this.
     * @param substitution some mapping
     * @return the mapped graph
     */
    private TerminationGraph mapGraph(final LinkedHashMap<IGeneralizedRule, IGeneralizedRule> substitution) {
        final LinkedHashSet<IGeneralizedRule> newNodes = TerminationGraph.mapSet(substitution, this.nodes);

        final TerminationGraph result = new TerminationGraph(newNodes, this.ng, this.aborter, this.proof);
        for (final Entry<IGeneralizedRule, LinkedHashSet<IGeneralizedRule>> e : this.edges.entrySet()) {
            IGeneralizedRule from = e.getKey();
            if (substitution.containsKey(from)) {
                from = substitution.get(from);
            }
            for (final IGeneralizedRule rule : e.getValue()) {
                IGeneralizedRule to = rule;
                if (substitution.containsKey(to)) {
                    to = substitution.get(to);
                }
                result.connect(from, to);
            }
        }
        return result;
    }

    /**
     * Applies chaining to simplify the intTRS.
     * @param scc the current scc
     * @return set of rules obtained by chaining
     */
    private Set<IGeneralizedRule> applyChaining(final Set<IGeneralizedRule> scc, final boolean defaultChainingOnly) {
        // Get a valid coloring:
        final Map<IGeneralizedRule, RedGrayBlue> coloring = this.calculateColoring();

        // Everything gray?
        boolean allGray = true;
        for (final Entry<IGeneralizedRule, RedGrayBlue> e : coloring.entrySet()) {
            if (e.getValue() != RedGrayBlue.GRAY) {
                allGray = false;
                break;
            }
        }

        if (!allGray && !defaultChainingOnly) {
            // No, then use color information:
            return this.coloredChaining(coloring);
        } else {
            // Yes, then use the default chaining:
            return this.defaultChaining(scc);
        }
    }

    /**
     * Applies the colored chaining: We can replace the red and blue rules by
     * the concatenation of blue rules and their successors.
     * @param coloring some valid coloring
     * @return set of rule obtained by the chaining
     */
    private Set<IGeneralizedRule> coloredChaining(final Map<IGeneralizedRule, RedGrayBlue> coloring) {
        final Set<IGeneralizedRule> newSCC = new LinkedHashSet<>();
        for (final Entry<IGeneralizedRule, RedGrayBlue> e : coloring.entrySet()) {
            if (e.getValue() == RedGrayBlue.GRAY) {
                newSCC.add(e.getKey());
            } else if (e.getValue() == RedGrayBlue.BLUE) {
                for (final IGeneralizedRule neighbour : this.edges.get(e.getKey())) {
                    final IGeneralizedRule newRule = new Chaining(e.getKey(), neighbour, this.ng).getResult();
                    newSCC.add(newRule);

                    this.proof.exportChaining(e.getKey(), neighbour, newRule);
                }
            }
        }
        return newSCC;
    }

    /**
     * Applies the default chaining: If one rule only has one successor, then we
     * can concatenate these rules. The picked rule can be dropped; while the
     * the successor rule can be dropped, if it has only the picked rule as
     * ancestor.
     * @param scc the current scc
     * @return set of rules obtained by chaining
     */
    private Set<IGeneralizedRule> defaultChaining(final Set<IGeneralizedRule> scc) {
        // Pick rule to drop:
        IGeneralizedRule pickedRule = scc.iterator().next();
        final int numberOfNeighbours = this.edges.get(pickedRule).size();

        for (final IGeneralizedRule node : scc) {
            final LinkedHashSet<IGeneralizedRule> neighbours = this.edges.get(node);
            if (neighbours.size() < numberOfNeighbours) {
                pickedRule = node;
                assert neighbours.size() != 0 : "Unexpected trivial SCC detected!";
            }
        }

        // Drop rule(s):
        final Set<IGeneralizedRule> newRules = new LinkedHashSet<>();
        final LinkedHashSet<IGeneralizedRule> neighbours = this.edges.get(pickedRule);

        for (final IGeneralizedRule neighbour : neighbours) {

            final IGeneralizedRule newRule = new Chaining(pickedRule, neighbour, this.ng).getResult();
            newRules.add(ToolBox.renameVariablesInRule(newRule, this.ng));

            this.proof.exportChaining(pickedRule, neighbour, newRule);
        }

        // The other rules are not touched, so we include them:
        for (final IGeneralizedRule iRule : scc) {
            if (iRule != pickedRule) {
                newRules.add(iRule);
            }
        }
        return newRules;
    }

    /**
     * Calculates a valid red-gray-blue-coloring. A coloring is valid, iff no
     * successor of a red (gray) [blue] node is red (red) [blue].
     * @return map from IGeneralizedRule to RedGrayBlue
     */
    private Map<IGeneralizedRule, RedGrayBlue> calculateColoring() {
        final LinkedHashMap<IGeneralizedRule, RedGrayBlue> coloring = new LinkedHashMap<>(this.nodes.size());

        IGeneralizedRule startNode = this.nodes.iterator().next();

        while (!this.colorRedBlue(coloring, new LinkedHashSet<IGeneralizedRule>(), startNode)) {

            // Remove all red and blue colors:
            final LinkedList<IGeneralizedRule> toBeReset = new LinkedList<>();
            for (final Entry<IGeneralizedRule, RedGrayBlue> e : coloring.entrySet()) {
                if (e.getValue() != RedGrayBlue.GRAY) {
                    toBeReset.add(e.getKey());
                } else {
                    startNode = e.getKey();
                }
            }
            for (final IGeneralizedRule key : toBeReset) {
                coloring.remove(key);
            }
        }

        assert this.checkColoring(coloring) : "Bug detected!";

        return coloring;
    }

    /**
     * Checks whether the given coloring is valid.
     * @param coloring given coloring
     * @return true iff the given coloring is valid
     */
    private boolean checkColoring(final LinkedHashMap<IGeneralizedRule, RedGrayBlue> coloring) {
        for (final Entry<IGeneralizedRule, RedGrayBlue> e : coloring.entrySet()) {
            final RedGrayBlue thisColor = e.getValue();
            if (thisColor == null) {
                return false;
            }

            for (final IGeneralizedRule succ : this.edges.get(e.getKey())) {
                final RedGrayBlue otherColor = coloring.get(succ);
                if (otherColor == null
                    || (thisColor == RedGrayBlue.BLUE && otherColor == RedGrayBlue.BLUE)
                    || (thisColor == RedGrayBlue.RED && otherColor == RedGrayBlue.RED)
                    || (thisColor == RedGrayBlue.GRAY && otherColor == RedGrayBlue.RED))
                {
                    return false;
                }
            }
        }

        return true;
    }

    /**
     * Tries to create a valid coloring using only red and blue. If this is not
     * possible, we color one conflict node gray and return false.
     * @param coloring maps rules to RedGrayBlue
     * @param visited set of visited nodes
     * @param currentNode the current node
     * @return true iff successful
     */
    private boolean colorRedBlue(
        final LinkedHashMap<IGeneralizedRule, RedGrayBlue> coloring,
        final LinkedHashSet<IGeneralizedRule> visited,
        final IGeneralizedRule currentNode)
    {
        if (visited.contains(currentNode)) {
            return true;
        }
        visited.add(currentNode);

        if (!coloring.containsKey(currentNode)) {
            coloring.put(currentNode, RedGrayBlue.BLUE);
        }

        // Get successor color:
        final RedGrayBlue currentColor = coloring.get(currentNode);
        final RedGrayBlue successorColor;
        if (currentColor == RedGrayBlue.GRAY || currentColor == RedGrayBlue.RED) {
            successorColor = RedGrayBlue.BLUE;
        } else if (currentColor == RedGrayBlue.BLUE) {
            successorColor = RedGrayBlue.RED;
        } else {
            assert false : "This is impossible!";
            successorColor = RedGrayBlue.BLUE;
        }

        // Color successors:
        for (final IGeneralizedRule succ : this.edges.get(currentNode)) {
            if (!coloring.containsKey(succ)) {
                // Node is uncolored, so we color it:
                coloring.put(succ, successorColor);
            } else if (coloring.get(succ) != RedGrayBlue.GRAY && coloring.get(succ) != successorColor) {
                // Color conflict detected, so we have to color one node gray:
                if (coloring.get(currentNode) == RedGrayBlue.GRAY) {
                    coloring.put(succ, RedGrayBlue.GRAY);
                } else {
                    coloring.put(currentNode, RedGrayBlue.GRAY);
                }
                return false;
            }
        }
        // Recursion:
        for (final IGeneralizedRule succ : this.edges.get(currentNode)) {
            if (!this.colorRedBlue(coloring, visited, succ)) {
                return false;
            }
        }

        return true;
    }

    /**
     * Returns the subgraph induced by [nodes]. Edges which do not start or end
     * in [nodes] will be discarded.
     * @param nodesSet set of nodes
     * @return a subgraph
     */
    public TerminationGraph getSubGraph(final Set<IGeneralizedRule> nodesSet) {
        final TerminationGraph result = new TerminationGraph(nodesSet, this.ng, this.aborter, this.proof);
        for (final IGeneralizedRule node : nodesSet) {
            for (final IGeneralizedRule neighbour : this.edges.get(node)) {
                if (nodesSet.contains(neighbour)) {
                    result.connect(node, neighbour);
                }
            }
        }
        return result;
    }

    /**
     * Calculate non-trivial SCCs. Uses Sharir's algorithm.
     */
    private void calculateSCCs() {
        // 1. Calculate topological order of the SCCs:
        // Please note, that we can compute this order without
        // having calculated the SCCs.
        this.nonTrivialSccs = new LinkedList<>();
        this.sccs = new LinkedList<>();
        LinkedHashSet<IGeneralizedRule> visited = new LinkedHashSet<>(this.nodes.size());
        final LinkedList<IGeneralizedRule> stack = new LinkedList<>();

        for (final IGeneralizedRule node : this.nodes) {
            if (!visited.contains(node)) {
                TerminationGraph.dfs(node, this.edges, visited, stack, null);
            }
        }

        // 2. Find SCCs:
        // Due to the topological order we know, that the nodes, which are
        // found in one step, belong to the same SCC.
        visited = new LinkedHashSet<>(this.nodes.size());
        while (!stack.isEmpty()) {
            final IGeneralizedRule node = stack.pop();
            if (visited.contains(node)) {
                continue;
            }

            // Discard trivial SCCs:
            final LinkedHashSet<IGeneralizedRule> scc = new LinkedHashSet<>();
            TerminationGraph.dfs(node, this.invertedEdges, visited, null, scc);
            boolean isTrivial = false;
            assert scc.size() > 0;
            if (scc.size() == 1) {
                final IGeneralizedRule singleNode = scc.iterator().next();
                isTrivial = !this.edges.get(singleNode).contains(singleNode);
            }

            this.sccs.add(scc);
            if (!isTrivial) {
                this.nonTrivialSccs.add(scc);
            }
        }
    }

    /**
     * Depth first search.
     * @param node where to start
     * @param currentEdges edges
     * @param visited set of visited nodes
     * @param stack stack to fill in finished nodes or null
     * @param found set to fill in found nodes or null
     */
    private static void dfs(
        final IGeneralizedRule node,
        final LinkedHashMap<IGeneralizedRule, LinkedHashSet<IGeneralizedRule>> currentEdges,
        final LinkedHashSet<IGeneralizedRule> visited,
        final LinkedList<IGeneralizedRule> stack,
        final LinkedHashSet<IGeneralizedRule> found)
    {
        visited.add(node);
        if (found != null) {
            found.add(node);
        }
        for (final IGeneralizedRule neighbour : currentEdges.get(node)) {
            if (!visited.contains(neighbour)) {
                TerminationGraph.dfs(neighbour, currentEdges, visited, stack, found);
            }
        }
        if (stack != null) {
            stack.push(node);
        }
    }

    /**
     * Returns a string representation of this.
     */
    @Override
    public String toString() {
        final StringBuilder result = new StringBuilder();
        result.append("Termination Graph:\n");
        result.append("Nodes:\n");

        final LinkedHashMap<IGeneralizedRule, Integer> numbers = new LinkedHashMap<>(this.nodes.size());
        int counter = 0;
        for (final IGeneralizedRule rule : this.nodes) {
            numbers.put(rule, counter);
            result.append("(" + counter + ") ").append(rule.toString()).append("\n");
            counter++;
        }

        result.append("Edges:\n");
        for (final Entry<IGeneralizedRule, LinkedHashSet<IGeneralizedRule>> e : this.edges.entrySet()) {
            final Integer from = numbers.get(e.getKey());
            for (final IGeneralizedRule toRule : e.getValue()) {
                final Integer to = numbers.get(toRule);
                result.append("(").append(from).append(") -> (").append(to).append(")\n");
            }
        }

        return result.toString();
    }
}
