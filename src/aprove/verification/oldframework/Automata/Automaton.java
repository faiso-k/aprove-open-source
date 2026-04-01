package aprove.verification.oldframework.Automata;

import java.util.*;

import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Every instance of this class represents a finite automaton. Every returned
 * automaton is a DFA where only letters (RegexpAtom) occur on the edges.
 * @author cotto
 * @param <N> the type of the nodes
 * @param <X> the alphabet used for the language accepted by this automaton
 */
public class Automaton<N, X> {
    /**
     * A very nice serial version UID.
     */
    private static final long serialVersionUID = 1L;

    /**
     * Create a new DFA out of the given graph, start state and accept states.
     * It is allowed that the input graph represents an epsilon-NFA.
     * @param <N> the type of the nodes
     * @param <X> the alphabet
     * @param graph a graph defining the transitions of an epsilon-NFA
     * @param start the start state
     * @param acceptStates the accept states
     * @return the corresponding DFA
     */
    public static <N, X> Automaton<N, X> create(final MultiGraph<N, Regexp<X>> graph,
        final Node<N> start,
        final Collection<Node<N>> acceptStates) {
        final Automaton<N, X> a = new Automaton<N, X>();
        a.graph = graph;
        a.startState = start;
        a.acceptStates = acceptStates;
        return a.det();
    }

    /**
     * @param regexp some regular expression.
     * @param <N> the type of the nodes
     * @param <X> the alphabet.
     * @return a DFA that accepts the same language as the given regexp.
     */
    public static <N, X> Automaton<N, X> create(final Regexp<X> regexp) {
        final Automaton<N, X> preResult = new Automaton<N, X>();
        final Pair<Node<N>, Node<N>> pair =
            preResult.addRegexp(regexp);
        preResult.startState = pair.x;
        preResult.addAcceptState(pair.y);
        return preResult.det();
    }

    /**
     * @param state some state
     * @param graph the graph representing the automaton containing the state
     * @param closures a map used to cache known closures
     * @return the epsilon closure for the given state
     * @param <N> the type of the nodes
     * @param <X> the alphabet
     */
    private static <N, X> Collection<Node<N>> epsilonClosure(final Node<N> state,
        final CollectionMap<Node<N>, Node<N>> closures,
        final MultiGraph<N, Regexp<X>> graph) {
        Collection<Node<N>> result = closures.get(state);
        if (result == null) {
            result = new LinkedHashSet<Node<N>>();
            final Stack<Node<N>> todo = new Stack<Node<N>>();
            todo.add(state);
            while (!todo.isEmpty()) {
                final Node<N> todoState = todo.pop();
                if (result.contains(todoState)) {
                    continue;
                }
                result.add(todoState);
                if (!graph.contains(todoState)) {
                    continue;
                }
                for (final EdgeEquality<Regexp<X>, N> edge : graph.getOutEdges(todoState)) {
                    final Node<N> endState = edge.getEndNode();
                    for (final Regexp<X> label : edge.getObject()) {
                        if (label instanceof RegexpEpsilon) {
                            todo.add(endState);
                        }
                    }
                }
            }
            closures.put(state, result);
        }
        return result;
    }

    /**
     * Create a new state for the given collection.
     * @param c some collection of states
     * @param graph the graph representing the automaton containing the states
     * @param newStates a map knowing about existing pairs
     * @return the corresponding state
     * @param <N> the type of the nodes
     * @param <X> the alphabet
     */
    private static <N, X> Node<N> getNewState(final Collection<Node<N>> c,
        final Map<Collection<Node<N>>, Node<N>> newStates,
        final MultiGraph<N, Regexp<X>> graph) {
        Node<N> result = newStates.get(c);
        if (result == null) {
            result = new Node<N>();
            graph.addNode(result);
            newStates.put(c, result);
        }
        return result;
    }

    /**
     * Construct the product automaton. The input automata must not contain
     * non-atomar edges.
     * @param a1 one of the two automata
     * @param a2 the other of the two automata
     * @return the resulting automaton.
     * @param <N> the type of the nodes
     * @param <X> the alphabet.
     */
    private static <N, X> Automaton<N, X> product(final Automaton<N, X> a1,
        final Automaton<N, X> a2) {
        final Map<Pair<Node<N>, Node<N>>, Node<N>> visited =
            new LinkedHashMap<Pair<Node<N>, Node<N>>, Node<N>>();
        final Automaton<N, X> result = new Automaton<N, X>();
        final Node<N> startState = new Node<N>();
        result.graph.addNode(startState);
        result.setStartState(startState);
        Automaton.product(a1, a1.getStartState(), a2, a2.getStartState(), result,
            startState, visited);
        return result;
    }

    /**
     * Recursively construct the product automaton.
     * @param <N> the type of the nodes
     * @param <X> the alphabet.
     * @param a1 some automaton
     * @param p the current state in a1
     * @param a2 also some automaton
     * @param q the current state in a2
     * @param res the resulting automaton
     * @param resState the current state in res
     * @param visited a map giving tuples (p, q, resState)
     */
    private static <N, X> void product(final Automaton<N, X> a1,
        final Node<N> p,
        final Automaton<N, X> a2,
        final Node<N> q,
        final Automaton<N, X> res,
        final Node<N> resState,
        final Map<Pair<Node<N>, Node<N>>, Node<N>> visited) {
        if (a1.acceptStates.contains(p) && a2.acceptStates.contains(q)) {
            res.addAcceptState(resState);
        }
        // for every outgoing edge in a1
        for (final EdgeEquality<Regexp<X>, N> e1 : a1.graph.getOutEdges(p)) {
            final Node<N> end1 = e1.getEndNode();
            for (final Regexp<X> regexp1 : e1.getObject()) {
                assert (regexp1 instanceof RegexpAtom);
                final RegexpAtom<X> atom1 = (RegexpAtom<X>) regexp1;

                // for every outgoing edge in a2
                for (final EdgeEquality<Regexp<X>, N> e2 : a2.graph.getOutEdges(q)) {
                    for (final Regexp<X> regexp2 : e2.getObject()) {
                        assert (regexp2 instanceof RegexpAtom);
                        final RegexpAtom<X> atom2 = (RegexpAtom<X>) regexp2;

                        // but only if the symbol is the same
                        if (atom1.equals(atom2)) {
                            final Node<N> end2 = e2.getEndNode();
                            final Pair<Node<N>, Node<N>> newPair =
                                new Pair<Node<N>, Node<N>>(end1, end2);
                            Node<N> newResState = visited.get(newPair);

                            // and we did not already follow these two edges
                            if (newResState == null) {
                                newResState = new Node<N>();
                                visited.put(newPair, newResState);
                                // add a new node for (p,q)
                                res.graph.addEdge(resState, newResState, atom1);
                                // and continue construction there
                                Automaton.product(a1, end1, a2, end2, res, newResState,
                                    visited);
                            } else {
                                // just add the edge, we already handled the target
                                res.graph.addEdge(resState, newResState, atom1);
                            }
                        }
                    }
                }
            }
        }
        return;
    }

    /**
     * The set of accept states.
     */
    private Collection<Node<N>> acceptStates;

    /**
     * The underying graph.
     */
    private MultiGraph<N, Regexp<X>> graph;

    /**
     * The (single) start state.
     */
    private Node<N> startState;

    /**
     * Create a DFA accepthing no word at all.
     */
    public Automaton() {
        this.graph = new MultiGraph<N, Regexp<X>>();
        this.acceptStates = new LinkedHashSet<Node<N>>();
    }

    /**
     * Mark the given state as an accept state.
     * @param state some state
     */
    private void addAcceptState(final Node<N> state) {
        this.acceptStates.add(state);
    }

    /**
     * Create an automaton accepting the language defined by the regular
     * expression. The resulting automaton only uses epsilon and letters for the
     * edge labels.
     * @param regexp the regexp to add
     * @return the start and end node created for the given regexp
     */
    private Pair<Node<N>, Node<N>> addRegexp(final Regexp<X> regexp) {
        final MultiGraph<N, Regexp<X>> g = this.graph;
        if (regexp instanceof RegexpAtom || regexp instanceof RegexpEpsilon) {
            final Node<N> start = new Node<N>();
            final Node<N> end = new Node<N>();
            g.addEdge(start, end, regexp);
            return new Pair<Node<N>, Node<N>>(start, end);
        } else if (regexp instanceof RegexpNAry) {
            final RegexpNAry<X> nAry = (RegexpNAry<X>) regexp;
            final Set<Regexp<X>> subs = nAry.getSubs();
            final Regexp<X> eps = RegexpEpsilon.create();
            if (nAry instanceof RegexpOr) {
                final Collection<Pair<Node<N>, Node<N>>> pairs =
                    new LinkedHashSet<Pair<Node<N>, Node<N>>>(
                        subs.size());
                for (final Regexp<X> sub : subs) {
                    pairs.add(this.addRegexp(sub));
                }
                final Node<N> start = new Node<N>();
                final Node<N> end = new Node<N>();
                for (final Pair<Node<N>, Node<N>> pair : pairs) {
                    g.addEdge(start, pair.x, eps);
                    g.addEdge(pair.y, end, eps);
                }
                return new Pair<Node<N>, Node<N>>(start, end);
            } else if (nAry instanceof RegexpAnd) {
                assert (!subs.isEmpty());
                Automaton<N, X> product = null;
                for (final Regexp<X> sub : subs) {
                    final Automaton<N, X> a = Automaton.create(sub);
                    if (product == null) {
                        product = a;
                    } else {
                        product = product.product(a);
                    }
                }
                assert (product != null);
                final Collection<Node<N>> endStates =
                    new LinkedHashSet<Node<N>>();
                Node<N> productStart = null;

                for (final EdgeEquality<Regexp<X>, N> edge : product.graph.getEdges()) {
                    final Node<N> start = edge.getStartNode();
                    final Node<N> end = edge.getEndNode();
                    for (final Regexp<X> label : edge.getObject()) {
                        if (product.startState.equals(start)) {
                            assert (productStart == null);
                            productStart = start;
                        }
                        if (product.isAcceptState(end)) {
                            endStates.add(end);
                        }
                        this.graph.addEdge(start, end, label);
                    }
                }
                final Node<N> newStart = new Node<N>();
                final Node<N> newEnd = new Node<N>();
                this.graph.addNode(newStart);
                this.graph.addNode(newEnd);
                this.graph.addEdge(newStart, productStart, eps);
                for (final Node<N> endState : endStates) {
                    this.graph.addEdge(endState, newEnd, eps);
                }
                return new Pair<Node<N>, Node<N>>(newStart, newEnd);
            }
        } else if (regexp instanceof RegexpConcat) {
            final RegexpConcat<X> concat = (RegexpConcat<X>) regexp;
            final Regexp<X> eps = RegexpEpsilon.create();
            final Regexp<X> sub1 = concat.getSubOne();
            final Regexp<X> sub2 = concat.getSubTwo();
            final Pair<Node<N>, Node<N>> pair1 = this.addRegexp(sub1);
            final Pair<Node<N>, Node<N>> pair2 = this.addRegexp(sub2);
            g.addEdge(pair1.y, pair2.x, eps);
            return new Pair<Node<N>, Node<N>>(pair1.x, pair2.y);
        } else if (regexp instanceof RegexpStar) {
            final Regexp<X> eps = RegexpEpsilon.create();
            final RegexpStar<X> star = (RegexpStar<X>) regexp;
            final Regexp<X> sub = star.getSub();
            final Pair<Node<N>, Node<N>> pair = this.addRegexp(sub);
            final Node<N> start = new Node<N>();
            final Node<N> end = new Node<N>();
            g.addEdge(start, pair.x, eps);
            g.addEdge(start, end, eps);
            g.addEdge(pair.y, pair.x, eps);
            g.addEdge(pair.y, end, eps);
            return new Pair<Node<N>, Node<N>>(start, end);
        } else if (regexp instanceof RegexpEmptyLanguage) {
            final Node<N> start = new Node<N>();
            final Node<N> end = new Node<N>();
            return new Pair<Node<N>, Node<N>>(start, end);
        }
        assert (false);
        return null;
    }

    /**
     * @param alphabet all letters of the alphabet
     * @return an automaton that accepts the complement of the language defined
     * by this.
     */
    public Automaton<N, X> complement(final Collection<Regexp<X>> alphabet) {
        final Automaton<N, X> det = this.det();
        final Collection<Node<N>> oldAcc =
            new LinkedHashSet<Node<N>>(det.acceptStates);
        det.acceptStates.addAll(det.graph.getNodes());
        det.acceptStates.removeAll(oldAcc);
        final Node<N> sinkState = new Node<N>();
        det.graph.addNode(sinkState);
        det.acceptStates.add(sinkState);
        for (final Node<N> node : det.graph.getNodes()) {
            // this copy will be modified
            final Collection<Regexp<X>> allLabels =
                new LinkedHashSet<Regexp<X>>(alphabet);
            for (final EdgeEquality<Regexp<X>, N> edge : det.graph.getOutEdges(node)) {
                allLabels.removeAll(edge.getObject());
            }
            // add edge to sink state for remaining labels
            for (final Regexp<X> label : allLabels) {
                det.graph.addEdge(node, sinkState, label);
            }
        }
        return det;
    }

    /**
     * @param other some automaton.
     * @return true iff the language defined by this automaton is a superset of
     * the language defined by the other automaton.
     */
    public boolean containsAll(final Automaton<N, X> other) {
        return this.containsAllCounterExample(other) == null;
    }

    /**
     * @param other some automaton.
     * @return null iff the language defined by this automaton is a superset of
     * the language defined by the other automaton. Otherwise a non-included
     * word is returned.
     */
    public List<X> containsAllCounterExample(final Automaton<N, X> other) {
        final Collection<Regexp<X>> alphabet = new LinkedHashSet<Regexp<X>>();
        alphabet.addAll(this.getAllLabels());
        alphabet.addAll(other.getAllLabels());
        final Automaton<N, X> complement = this.complement(alphabet);
        final Automaton<N, X> product = complement.product(other);
        return product.emptyLanguageCounterExample();
    }

    /**
     * @return an equivalent DFA.
     */
    private Automaton<N, X> det() {
        final CollectionMap<Node<N>, Node<N>> closures =
            new CollectionMap<Node<N>, Node<N>>();
        final Map<Collection<Node<N>>, Node<N>> newStates =
            new LinkedHashMap<Collection<Node<N>>, Node<N>>();

        // Initialize resulting automaton and add start state
        final Automaton<N, X> result = new Automaton<N, X>();
        final Collection<Node<N>> startClosure =
            Automaton.epsilonClosure(this.startState, closures, this.graph);
        final Node<N> detStartState =
            Automaton.getNewState(startClosure, newStates, result.graph);
        result.setStartState(detStartState);
        newStates.put(startClosure, detStartState);

        // add accept states and transitions
        final Stack<Collection<Node<N>>> todoStates =
            new Stack<Collection<Node<N>>>();
        final Collection<Collection<Node<N>>> done =
            new LinkedHashSet<Collection<Node<N>>>();
        todoStates.add(startClosure);
        while (!todoStates.isEmpty()) {
            final Collection<Node<N>> collection = todoStates.pop();
            if (done.contains(collection)) {
                continue;
            }
            done.add(collection);
            final Node<N> newState =
                Automaton.getNewState(collection, newStates, result.graph);
            boolean acceptState = false;
            /*
             * for each label collect the reachable states (and their
             * epsilon closure)
             */
            final CollectionMap<Regexp<X>, Node<N>> targetsByLabel =
                new CollectionMap<Regexp<X>, Node<N>>();
            for (final Node<N> state : collection) {
                if (!acceptState && this.isAcceptState(state)) {
                    acceptState = true;
                    result.addAcceptState(newState);
                }

                if (!this.graph.contains(state)) {
                    continue;
                }
                for (final EdgeEquality<Regexp<X>, N> edge : this.graph.getOutEdges(state)) {
                    final Node<N> endState = edge.getEndNode();
                    for (final Regexp<X> edgeLabel : edge.getObject()) {
                        if (edgeLabel instanceof RegexpEpsilon) {
                            continue;
                        }
                        assert (edgeLabel instanceof RegexpAtom);
                        targetsByLabel.add(edgeLabel, Automaton.epsilonClosure(
                            endState, closures, this.graph));
                    }
                }
            }

            for (final Map.Entry<Regexp<X>, Collection<Node<N>>> entry : targetsByLabel.entrySet()) {
                final Collection<Node<N>> targets = entry.getValue();
                // continue construction in the calculated set of states
                todoStates.add(targets);
                final Regexp<X> edgeLabel = entry.getKey();
                final Node<N> newStateForCollection =
                    Automaton.getNewState(targets, newStates, result.graph);
                result.graph.addEdge(newState, newStateForCollection, edgeLabel);
            }
        }

        return result;
    }

    /**
     * @return true iff the language defined by this automaton is empty.
     */
    public boolean emptyLanguage() {
        return this.emptyLanguageCounterExample() == null;
    }

    /**
     * @return null if the language is empty. Otherwise a word in the langauge
     * is returned.
     */
    private List<X> emptyLanguageCounterExample() {
        if (this.acceptStates.isEmpty()) {
            return null;
        }
        for (final Node<N> acc : this.acceptStates) {
            final List<Node<N>> path =
                this.graph.getPath(this.startState, acc);
            if (path != null) {
                final List<X> word = new LinkedList<X>();
                Node<N> prev = null;
                for (final Node<N> node : path) {
                    if (prev != null) {
                        final EdgeEquality<Regexp<X>, N> edge =
                            this.graph.getEdge(prev, node);
                        for (final Regexp<X> r : edge.getObject()) {
                            if (r instanceof RegexpAtom) {
                                final RegexpAtom<X> atom = (RegexpAtom<X>) r;
                                word.add(atom.getLetter());
                                break;
                            }
                        }
                    }
                    prev = node;
                }
                return word;
            }
        }
        return null;
    }

    /**
     * @return all labels that occur in this automaton
     */
    private Collection<Regexp<X>> getAllLabels() {
        final Collection<Regexp<X>> result = new LinkedHashSet<Regexp<X>>();
        for (final EdgeEquality<Regexp<X>, N> edge : this.graph.getEdges()) {
            for (final Regexp<X> label : edge.getObject()) {
                if (label instanceof RegexpAtom<?>) {
                    result.add(label);
                } else if (label instanceof RegexpEpsilon<?>) {
                    continue;
                } else {
                    assert (false);
                }
            }
        }
        return result;
    }

    /**
     * @return the start state.
     */
    private Node<N> getStartState() {
        assert (this.startState != null);
        return this.startState;
    }

    /**
     * @return true iff the given state is an accept state.
     * @param state some state
     */
    private boolean isAcceptState(final Node<N> state) {
        return this.acceptStates.contains(state);
    }

    /**
     * @param other some automaton
     * @return an automaton which accepts the intersection of the languages
     * defined buy this automaton and by the given other automaton.
     */
    public Automaton<N, X> product(final Automaton<N, X> other) {
        final Automaton<N, X> product = Automaton.product(this, other);
        return product;
    }

    /**
     * Set the given state as start state.
     * @param start some state
     */
    public void setStartState(final Node<N> start) {
        this.startState = start;
    }

    /**
     * @return a semi-nice string representation
     */
    @Override
    public String toString() {
        return "Start state: " + this.startState.toString()
            + "\nAccept states: " + this.acceptStates.toString()
            + "\nTransitions:\n" + this.graph.toString();
    }

    /**
     * @return a regular expression accepting the language of this automaton
     */
    public Regexp<X> toRegexp() {
        final Automaton<N, X> work = this.det();
        final Node<N> newStart = new Node<N>();
        final Node<N> newAccept = new Node<N>();
        final Regexp<X> eps = RegexpEpsilon.create();
        work.graph.addEdge(newStart, work.getStartState(), eps);
        work.setStartState(newStart);
        for (final Node<N> oldAccept : work.acceptStates) {
            work.graph.addEdge(oldAccept, newAccept, eps);
        }
        work.acceptStates.clear();
        work.acceptStates.add(newAccept);
        final Stack<Node<N>> todo = new Stack<Node<N>>();
        todo.addAll(work.graph.getNodes());
        todo.remove(newStart);
        todo.remove(newAccept);
        while (!todo.isEmpty()) {
            final Node<N> node = todo.pop();
            Regexp<X> middleToMiddleRegexp = RegexpEmptyLanguage.create();
            final EdgeEquality<Regexp<X>, N> loop =
                work.graph.getEdge(node, node);
            if (loop != null) {
                middleToMiddleRegexp = RegexpOr.create(loop.getObject());
            }
            for (final EdgeEquality<Regexp<X>, N> inEdge : new LinkedList<EdgeEquality<Regexp<X>, N>>(
                work.graph.getInEdges(node))) {
                final Node<N> startNode = inEdge.getStartNode();
                if (startNode.equals(node)) {
                    continue;
                }
                for (final EdgeEquality<Regexp<X>, N> outEdge : new LinkedList<EdgeEquality<Regexp<X>, N>>(
                    work.graph.getOutEdges(node))) {
                    final Node<N> endNode = outEdge.getEndNode();
                    if (endNode.equals(node)) {
                        continue;
                    }
                    Regexp<X> startToEndRegexp = RegexpEmptyLanguage.create();
                    final EdgeEquality<Regexp<X>, N> startToEndEdge =
                        work.graph.getEdge(startNode, endNode);
                    if (startToEndEdge != null) {
                        final Collection<Regexp<X>> startToEndRegexps =
                            startToEndEdge.getObject();
                        startToEndRegexp = RegexpOr.create(startToEndRegexps);
                    }
                    final Regexp<X> startToMiddleRegexp =
                        RegexpOr.create(inEdge.getObject());
                    final Regexp<X> middleToEndRegexp =
                        RegexpOr.create(outEdge.getObject());
                    final Regexp<X> newLabel =
                        startToEndRegexp.or(startToMiddleRegexp.concat(middleToMiddleRegexp.star().concat(
                            middleToEndRegexp)));
                    if (!(newLabel instanceof RegexpEmptyLanguage)) {
                        work.graph.addEdge(startNode, endNode, newLabel);
                    }
                }
            }
            work.graph.removeNode(node);
        }
        final EdgeEquality<Regexp<X>, N> resultEdge =
            work.graph.getEdge(newStart, newAccept);
        Regexp<X> result = RegexpEmptyLanguage.create();
        if (resultEdge != null) {
            result = resultEdge.getObject().iterator().next();
        }
        return result;
    }
}
