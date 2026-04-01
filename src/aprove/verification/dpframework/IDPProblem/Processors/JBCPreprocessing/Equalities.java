package aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Automata.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Instances of this class are used to denote which arguments for the two
 * function symbols are equal.
 * @author cotto
 */
public class Equalities
        extends
        LinkedHashMap<FunctionSymbol, Map<FunctionSymbol, CollectionMap<Integer, Integer>>> {

    /**
     * Yeah. As If.
     */
    private static final long serialVersionUID = 6609784148955655372L;

    /**
     * If the corresponding map does not exist yet, it will be created with
     * default values (everything equal). For f->f only "straight edges" are
     * marked as equal.
     * @param fsL the left function symbol
     * @param fsR the right function symbol
     * @return the arg->arg map for the two given function symbols.
     */
    public CollectionMap<Integer, Integer> get(final FunctionSymbol fsL,
        final FunctionSymbol fsR) {
        Map<FunctionSymbol, CollectionMap<Integer, Integer>> mapForLeftFS =
            this.get(fsL);
        if (mapForLeftFS == null) {
            mapForLeftFS =
                new LinkedHashMap<FunctionSymbol, CollectionMap<Integer, Integer>>();
            this.put(fsL, mapForLeftFS);
        }
        final int arityL = fsL.getArity();
        final int arityR = fsR.getArity();
        CollectionMap<Integer, Integer> eqMap = mapForLeftFS.get(fsR);
        if (eqMap == null) {
            /*
             * Initially every edge denotes equality. For f(..) -> f(...)
             * we are only interested in the equalities that hold for an
             * arbitrary number of iterations (so: i -> i, not i -> j with
             * i != j).
             */
            eqMap = new CollectionMap<Integer, Integer>();
            if (fsL.equals(fsR)) {
                for (int i = 0; i < arityL; i++) {
                    final Integer leftInteger = Integer.valueOf(i);
                    eqMap.add(leftInteger, leftInteger);
                }
            } else {
                for (int i = 0; i < arityL; i++) {
                    final Integer leftInteger = Integer.valueOf(i);
                    for (int j = 0; j < arityR; j++) {
                        final Integer rightInteger = Integer.valueOf(j);
                        eqMap.add(leftInteger, rightInteger);
                    }
                }
            }
            mapForLeftFS.put(fsR, eqMap);
        }
        return eqMap;
    }

    /**
     * @param subs several maps.
     * @return only the edges that exist in every given map.
     */
    private CollectionMap<Integer, Integer> intersect(final Collection<CollectionMap<Integer, Integer>> subs) {
        if (subs.isEmpty()) {
            return null;
        }
        final Iterator<CollectionMap<Integer, Integer>> it =
            subs.iterator();
        CollectionMap<Integer, Integer> result = it.next();
        while (it.hasNext()) {
            result = this.binaryIntersect(result, it.next());
        }
        return result;
    }

    /**
     * @param left a map
     * @param right another map
     * @return only the edges that exist in both maps.
     */
    private CollectionMap<Integer, Integer> binaryIntersect(final CollectionMap<Integer, Integer> left,
        final CollectionMap<Integer, Integer> right) {
        final CollectionMap<Integer, Integer> result =
            new CollectionMap<Integer, Integer>();
        for (final Map.Entry<Integer, Collection<Integer>> entry : left.entrySet()) {
            final Integer key = entry.getKey();
            final Collection<Integer> rightTargets = right.get(key);
            if (rightTargets == null) {
                continue;
            }
            for (final Integer value : entry.getValue()) {
                if (rightTargets.contains(value)) {
                    result.add(key, value);
                }
            }
        }
        return result;
    }

    /**
     * Glue the two collections together.
     * @param left the map for X -> Y
     * @param right the map for Y -> Z
     * @return the map for X -> Z
     */
    private CollectionMap<Integer, Integer> merge(final CollectionMap<Integer, Integer> left,
        final CollectionMap<Integer, Integer> right) {
        if (left == null) {
            if (right == null) {
                return null;
            }
            return right;
        }
        final CollectionMap<Integer, Integer> result =
            new CollectionMap<Integer, Integer>();
        for (final Map.Entry<Integer, Collection<Integer>> entry : left.entrySet()) {
            final Integer key = entry.getKey();
            for (final Integer middle : entry.getValue()) {
                final Collection<Integer> rightCollection =
                    right.getNotNull(middle);
                result.add(key, rightCollection);
            }
        }
        return result;
    }

    /**
     * Walk through the graph and gather the unchanged positions.
     * @param subGraph the current graph
     * @param unchangedPositions a map defining all unchanged positions for
     * each function symbol
     */
    public void puzzleTogether(final MultiGraph<FunctionSymbol, GeneralizedRule> subGraph,
        final CollectionMap<FunctionSymbol, Integer> unchangedPositions) {
        final MultiGraph<FunctionSymbol, Regexp<CollectionMap<Integer, Integer>>> graph =
            new MultiGraph<FunctionSymbol, Regexp<CollectionMap<Integer, Integer>>>();
        final Map<FunctionSymbol, Node<FunctionSymbol>> fsToNode =
            new LinkedHashMap<FunctionSymbol, Node<FunctionSymbol>>();
        final CollectionMap<FunctionSymbol, GeneralizedRule> rules =
            new CollectionMap<FunctionSymbol, GeneralizedRule>();
        /*
         * First create a slightly different graph, where the edge is
         * labelled with the "unchanged edge" maps.
         */
        for (final EdgeEquality<GeneralizedRule, FunctionSymbol> edge : subGraph.getEdges()) {
            final Node<FunctionSymbol> from = edge.getStartNode();
            final Node<FunctionSymbol> to = edge.getEndNode();
            final FunctionSymbol fsL = from.getObject();
            final FunctionSymbol fsR = to.getObject();
            rules.add(fsL, edge.getObject());
            final CollectionMap<Integer, Integer> atom = this.get(fsL, fsR);
            final Regexp<CollectionMap<Integer, Integer>> regexp =
                new RegexpAtom<CollectionMap<Integer, Integer>>(atom);
            Node<FunctionSymbol> fromNode = fsToNode.get(fsL);
            if (fromNode == null) {
                fromNode = new Node<FunctionSymbol>(fsL);
                fsToNode.put(fsL, fromNode);
            }
            Node<FunctionSymbol> toNode = fsToNode.get(fsR);
            if (toNode == null) {
                toNode = new Node<FunctionSymbol>(fsR);
                fsToNode.put(fsR, toNode);
            }
            graph.addEdge(fromNode, toNode, regexp);
        }

        /*
         * Now start with some node of the SCC and find out which arguments
         * survive a trip through the whole SCC. For this, we fold the
         * "unchanged edge" maps using a transformation of the graph to a
         * regular expression describing all paths through the graph
         * (automaton to regexp).
         */
        final Node<FunctionSymbol> startNode =
            fsToNode.values().iterator().next();
        final Collection<Node<FunctionSymbol>> acceptStates =
            Collections.singleton(startNode);
        final Automaton<FunctionSymbol, CollectionMap<Integer, Integer>> automaton =
            Automaton.create(graph, startNode, acceptStates);
        final Regexp<CollectionMap<Integer, Integer>> re =
            automaton.toRegexp(); // This is the important step

        // Create a single map out of the regexp
        final CollectionMap<Integer, Integer> unchanged = this.merge(re);

        /*
         * Now, for each unchanged argument, have a look at all nodes in the
         * SCC and check that the variable is used nowhere. If it is used,
         * it may not be removed.
         */
        for (final Map.Entry<Integer, Collection<Integer>> entry : unchanged.entrySet()) {
            if (entry.getValue().isEmpty()) {
                continue;
            }
            final Integer pos = entry.getKey();
            final Collection<Pair<Node<FunctionSymbol>, Integer>> seen =
                new LinkedHashSet<Pair<Node<FunctionSymbol>, Integer>>();
            if (this.check(graph, startNode, rules, pos, seen)) {
                for (final Pair<Node<FunctionSymbol>, Integer> pair : seen) {
                    final FunctionSymbol fs = pair.x.getObject();
                    unchangedPositions.add(fs, pair.y);
                }
            }
        }
    }

    /**
     * Go through the whole SCC, starting with the given function symbol and
     * a position. For every reachable RHS check that the (unchanged)
     * variable defined by the position in the LHS is not used inside some
     * non-root function application.
     * @param graph the graph corresponding to the itrs
     * @param startNode the node where to start checking
     * @param rules information about rules starting with the given function
     * symbol
     * @param pos the positition to check
     * @param seen information about visited positions
     * @rules a map giving all rules starting with the given function symbol
     * @return true if, when walking through the graph starting in the
     * startNode at the given position, the arguments along this path are
     * not used in some fancy way.
     */
    private boolean check(final MultiGraph<FunctionSymbol, Regexp<CollectionMap<Integer, Integer>>> graph,
        final Node<FunctionSymbol> startNode,
        final CollectionMap<FunctionSymbol, GeneralizedRule> rules,
        final Integer pos,
        final Collection<Pair<Node<FunctionSymbol>, Integer>> seen) {
        final Stack<Pair<Node<FunctionSymbol>, Integer>> todo =
            new Stack<Pair<Node<FunctionSymbol>, Integer>>();
        final Pair<Node<FunctionSymbol>, Integer> todoPair =
            new Pair<Node<FunctionSymbol>, Integer>(startNode, pos);
        todo.add(todoPair);
        while (!todo.isEmpty()) {
            final Pair<Node<FunctionSymbol>, Integer> pair = todo.pop();
            if (seen.contains(pair)) {
                continue;
            }
            seen.add(pair);
            final Node<FunctionSymbol> currentNode = pair.x;
            final FunctionSymbol leftFS = currentNode.getObject();
            final Integer leftPos = pair.y;
            for (final GeneralizedRule rule : rules.get(leftFS)) {
                final TRSFunctionApplication rightFA =
                    (TRSFunctionApplication) rule.getRight();
                final TRSTerm argLeft =
                    rule.getLeft().getArgument(leftPos.intValue());
                if (!argLeft.isVariable()) {
                    return false;
                }
                final TRSVariable varLeft = (TRSVariable) argLeft;
                for (final TRSTerm rightArg : rightFA.getArguments()) {
                    if (rightArg.isVariable()) {
                        continue;
                    }
                    final TRSFunctionApplication argFA =
                        (TRSFunctionApplication) rightArg;
                    if (argFA.getVariables().contains(varLeft)) {
                        return false;
                    }
                }
            }
            for (final EdgeEquality<Regexp<CollectionMap<Integer, Integer>>, FunctionSymbol> outEdge : graph.getOutEdges(currentNode)) {
                final Node<FunctionSymbol> endNode = outEdge.getEndNode();
                final CollectionMap<Integer, Integer> map =
                    this.get(leftFS, outEdge.getEndNode().getObject());
                assert (map.containsKey(leftPos));
                for (final Integer rightPos : map.get(leftPos)) {
                    final Pair<Node<FunctionSymbol>, Integer> newPair =
                        new Pair<Node<FunctionSymbol>, Integer>(endNode,
                            rightPos);
                    todo.add(newPair);
                }
            }
        }
        return true;
    }

    /**
    * Convert the complex regexp to a map. Here, x or y is handled as the
    * intersection, x.y (concatenation) is restriction to paths going from
    * the left of x to the right of y.
    * @param regexp a regexp over maps.
    * @return the map corresponding to the regexp.
    */
    private CollectionMap<Integer, Integer> merge(final Regexp<CollectionMap<Integer, Integer>> regexp) {
        if (regexp instanceof RegexpAtom) {
            final RegexpAtom<CollectionMap<Integer, Integer>> atom =
                (RegexpAtom<CollectionMap<Integer, Integer>>) regexp;
            return atom.getLetter();
        } else if (regexp instanceof RegexpEmptyLanguage) {
            assert (false);
            return null;
        } else if (regexp instanceof RegexpEpsilon) {
            return null;
        } else if (regexp instanceof RegexpAnd) {
            assert (false);
            return null;
        } else if (regexp instanceof RegexpStar) {
            final Regexp<CollectionMap<Integer, Integer>> sub =
                ((RegexpStar<CollectionMap<Integer, Integer>>) regexp).getSub();
            final CollectionMap<Integer, Integer> mergedSub = this.merge(sub);
            return this.star(mergedSub);
        } else if (regexp instanceof RegexpOr) {
            final RegexpOr<CollectionMap<Integer, Integer>> regexpOr =
                (RegexpOr<CollectionMap<Integer, Integer>>) regexp;
            final Collection<CollectionMap<Integer, Integer>> subs =
                new LinkedHashSet<CollectionMap<Integer, Integer>>();
            for (final Regexp<CollectionMap<Integer, Integer>> sub : regexpOr.getSubs()) {
                final CollectionMap<Integer, Integer> merged = this.merge(sub);
                if (merged != null) {
                    subs.add(merged);
                }
            }
            return this.intersect(subs);
        } else if (regexp instanceof RegexpConcat) {
            final RegexpConcat<CollectionMap<Integer, Integer>> regexpConcat =
                (RegexpConcat<CollectionMap<Integer, Integer>>) regexp;
            final Regexp<CollectionMap<Integer, Integer>> subOne =
                regexpConcat.getSubOne();
            final Regexp<CollectionMap<Integer, Integer>> subTwo =
                regexpConcat.getSubTwo();
            return this.merge(this.merge(subOne), this.merge(subTwo));
        }
        assert (false);
        return null;
    }

    /**
     * Restrict the map to straight paths.
     * @param map a map of paths.
     * @return the restriction to straight paths.
     */
    private CollectionMap<Integer, Integer> star(final CollectionMap<Integer, Integer> map) {
        if (map == null) {
            return null;
        }
        final CollectionMap<Integer, Integer> result =
            new CollectionMap<Integer, Integer>();
        for (final Map.Entry<Integer, Collection<Integer>> entry : map.entrySet()) {
            final Integer key = entry.getKey();
            if (entry.getValue().contains(key)) {
                result.add(key, key);
            }
        }
        return result;
    }

    /**
     * For the two given function applications, restrict the corresponding
     * map to the arguments that are left unchanged.
     * @param lhsFA a function application
     * @param rhsFA another function application
     */
    void equalityForRule(final TRSFunctionApplication lhsFA,
        final TRSFunctionApplication rhsFA) {
        final FunctionSymbol fsL = lhsFA.getRootSymbol();
        final FunctionSymbol fsR = rhsFA.getRootSymbol();
        final CollectionMap<Integer, Integer> eqMap = this.get(fsL, fsR);

        for (final Map.Entry<Integer, Collection<Integer>> entry : eqMap.entrySet()) {
            final Integer leftInteger = entry.getKey();
            final TRSTerm termLeft = lhsFA.getArgument(leftInteger.intValue());
            if (!termLeft.isVariable()) {
                entry.getValue().clear();
                continue;
            }
            final Collection<Integer> value = entry.getValue();
            for (final Integer rightInteger : new LinkedList<Integer>(value)) {
                final TRSTerm termRight =
                    rhsFA.getArgument(rightInteger.intValue());
                if (!termLeft.equals(termRight)) {
                    value.remove(rightInteger);
                }
            }
        }
    }
}
