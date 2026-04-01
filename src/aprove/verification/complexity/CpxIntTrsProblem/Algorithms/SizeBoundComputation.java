package aprove.verification.complexity.CpxIntTrsProblem.Algorithms;

import java.util.*;
import java.util.Map.Entry;

import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.LocalComplexityValue.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class SizeBoundComputation {

    private static Node<CallArgument> getNode(Map<CallArgument, Node<CallArgument>> nodes, CallArgument pos) {
        Node<CallArgument> node = nodes.get(pos);
        if (node == null) {
            node = new Node<>(pos);
            nodes.put(pos, node);
        }
        return node;
    }

    public static CallArgumentGraph buildCallArgumentGraph(CpxIntGraph graph, Abortion aborter)
        throws AbortionException
    {
        Map<CallArgument, Node<CallArgument>> nodes = new LinkedHashMap<>();
        CallArgumentGraph g = new CallArgumentGraph();

        Set<CallArgument> positions = new LinkedHashSet<>();
        for (CpxIntTupleRule rule : graph.getRules()) {
            positions.addAll(rule.getLocalSizeBounds(aborter).keySet());
        }
        for (CallArgument pos : positions) {
            g.addNode(SizeBoundComputation.getNode(nodes, pos));
        }

        for (CallArgument fromPos : positions) {
            for (CpxIntTupleRule toRule : graph.getOut(fromPos.rule, fromPos.rhs)) {
                ImmutableLinkedHashMap<Integer, ImmutableLinkedHashSet<CallArgument>> sizedeps =
                    toRule.getSizeDependencies(aborter);
                for (CallArgument toPos : sizedeps.get(fromPos.argument)) {
                    g.addEdge(SizeBoundComputation.getNode(nodes, fromPos), SizeBoundComputation.getNode(nodes, toPos));
                }
            }
        }
        return g;
    }

    public static ImmutableLinkedHashMap<CallArgument, LocalComplexityValue> computeSizeBounds(
        CpxIntTrsProblem obl,
        Abortion aborter) throws AbortionException
    {
        Graph<CallArgument, Void> graph = SizeBoundComputation.buildCallArgumentGraph(obl.getDepGraph(aborter), aborter);
        ImmutableLinkedHashSet<FunctionSymbol> G = obl.getG();
        ImmutableLinkedHashMap<CpxIntTupleRule, ComplexityValue> K = obl.getK();

        // compute *all* SCCs in reverse topological order
        LinkedHashSet<Cycle<CallArgument>> reversed_sccs = graph.getSCCs(false);
        ArrayList<Cycle<CallArgument>> sccs = new ArrayList<>();
        // now obtain the topological order by reversing
        sccs.addAll(reversed_sccs);
        Collections.reverse(sccs);

        // compute predecessor mapping for condensation of call argument graph
        LinkedHashMap<Cycle<CallArgument>, LinkedHashSet<Cycle<CallArgument>>> preds = new LinkedHashMap<>();
        LinkedHashMap<CallArgument, Cycle<CallArgument>> cycles = new LinkedHashMap<>();
        for (Cycle<CallArgument> scc : sccs) {
            LinkedHashSet<Cycle<CallArgument>> ps = new LinkedHashSet<>();
            for (CallArgument alpha : scc.getNodeObjects()) {
                cycles.put(alpha, scc);
                for (Node<CallArgument> node : graph.getIn(graph.getNodeFromObject(alpha))) {
                    CallArgument pred = node.getObject();
                    if (scc.contains(graph.getNodeFromObject(pred))) {
                        continue;
                    }
                    Cycle<CallArgument> cycle = cycles.get(pred);
                    assert cycle != null;
                    if (!cycle.equals(scc)) {
                        ps.add(cycle);
                    }
                }
            }
            preds.put(scc, ps);
        }

        LinkedHashMap<Cycle<CallArgument>, LocalComplexityValue> globalComplAkk = new LinkedHashMap<>();

        for (Cycle<CallArgument> scc : sccs) {
            LocalComplexityValue c = SizeBoundComputation.computeSCC(scc, preds, G, K, graph, globalComplAkk, aborter);
            globalComplAkk.put(scc, c);
        }

        LinkedHashMap<CallArgument, LocalComplexityValue> globalComplexityFunction = new LinkedHashMap<>();
        for (Entry<Cycle<CallArgument>, LocalComplexityValue> e : globalComplAkk.entrySet()) {
            LocalComplexityValue cv = e.getValue();
            for (CallArgument alpha : e.getKey().getNodeObjects()) {
                globalComplexityFunction.put(alpha, cv);
            }
        }
        return ImmutableCreator.create(globalComplexityFunction);
    }

    private static LocalComplexityValue computeSCC(
        Cycle<CallArgument> scc,
        LinkedHashMap<Cycle<CallArgument>, LinkedHashSet<Cycle<CallArgument>>> preds,
        ImmutableLinkedHashSet<FunctionSymbol> G,
        ImmutableLinkedHashMap<CpxIntTupleRule, ComplexityValue> K,
        Graph<CallArgument, Void> graph,
        LinkedHashMap<Cycle<CallArgument>, LocalComplexityValue> globalComplAkk,
        Abortion aborter)
    {
        LocalComplexityValue b_prime = LocalComplexityValue.POL0;
        for (Cycle<CallArgument> n_i : preds.get(scc)) {
            LocalComplexityValue n_i_c = globalComplAkk.get(n_i);
            assert n_i_c != null;
            b_prime = b_prime.max(n_i_c);
        }

        // compute max {b_alpha | "a | b_alpha" is a node in n }
        LocalComplexityValue max_n = LocalComplexityValue.POL0;
        for (CallArgument alpha : scc.getNodeObjects()) {
            LocalComplexityValue b_alpha = alpha.getLocalSizeBound(aborter).getC();
            max_n = max_n.max(b_alpha);
        }

        // first case
        if (LocalComplexityValue.POL0.equals(max_n)) {
            return LocalComplexityValue.POL0;
        }

        boolean containsStartNode = false;
        for (Node<CallArgument> n : scc) {
            FunctionSymbol fs = n.getObject().rule.getRootSymbol();
            if (G.contains(fs)) {
                containsStartNode = true;
                break;
            }
        }

        // second case
        if (LocalComplexityValue.EQUALITYBOUND.equals(max_n)) {
            if (!containsStartNode) {
                return b_prime;
            } else {
                return LocalComplexityValue.EQUALITYBOUND.max(b_prime);
            }
        }

        boolean trivial = preds.get(scc).contains(scc);

        // third case
        if (LocalComplexityValue.ADDCONSTANTBOUND.equals(max_n)) {
            if (trivial) {
                if (b_prime.equals(LocalComplexityValue.POL0) && !containsStartNode) {
                    return LocalComplexityValue.POL0;
                } else {
                    return LocalComplexityValue.ADDCONSTANTBOUND.max(b_prime);
                }
            } else {
                LocalComplexityValue b_addConstant = LocalComplexityValue.POL0;
                for (CallArgument n : scc.getNodeObjects()) {
                    LocalSizeBound lsb = n.getLocalSizeBound(aborter);
                    if (!LocalComplexityValue.ADDCONSTANTBOUND.equals(lsb.getC())) {
                        continue;
                    }
                    CpxIntTupleRule rho = n.rule;
                    b_addConstant = b_addConstant.max(LocalComplexityValue.fromComplexityValue(K.get(rho)));
                }
                return LocalComplexityValue.ADDCONSTANTBOUND.max(b_addConstant).max(b_prime);
            }
        }

        // fourth case
        if (max_n instanceof PolynomialBound) {
            Integer i = max_n.getDegree();
            assert i != 0; // this case was handled above
            if (!trivial) {
                return LocalComplexityValue.UNBOUNDED;
            }
            if (LocalComplexityValue.POL0.equals(b_prime)) {
                if (containsStartNode) {
                    return max_n;
                } else {
                    return LocalComplexityValue.POL0;
                }
            }
            if (LocalComplexityValue.EQUALITYBOUND.equals(b_prime)
                || LocalComplexityValue.ADDCONSTANTBOUND.equals(b_prime)
                || LocalComplexityValue.ADDBOUND.equals(b_prime))
            {
                return max_n;
            }
            if (b_prime instanceof PolynomialBound) {
                Integer j = b_prime.getDegree();
                assert j != 0; // this case was handled above
                return LocalComplexityValue.createPolBound(i * j);
            }
            if (LocalComplexityValue.UNBOUNDED.equals(b_prime)) {
                return LocalComplexityValue.UNBOUNDED;
            }
            throw new RuntimeException("should not happe");
        }

        // fifth case
        if (LocalComplexityValue.UNBOUNDED.equals(max_n)) {
            return LocalComplexityValue.UNBOUNDED;
        }

        if (LocalComplexityValue.ADDBOUND.equals(max_n)) {

            LinkedHashSet<Node<CallArgument>> addBoundNodes = new LinkedHashSet<>();
            for (Node<CallArgument> alpha : scc) {
                LocalComplexityValue b_alpha = alpha.getObject().getLocalSizeBound(aborter).getC();
                if (!LocalComplexityValue.ADDBOUND.equals(b_alpha)) {
                    continue;
                }
                addBoundNodes.add(alpha);
            }

            boolean two_bad_incoming_edges = false;
            scc_nodes: for (Node<CallArgument> alpha : addBoundNodes) {
                HashSet<Pair<CpxIntTupleRule, Integer>> incoming = new HashSet<>();
                // check all predecessors
                for (Node<CallArgument> pre : graph.getIn(alpha)) {
                    if (!scc.contains(pre)) {
                        continue;
                    }
                    CallArgument ca = pre.getObject();
                    boolean not_contained = incoming.add(new Pair<>(ca.rule, ca.rhs));
                    if (!not_contained) {
                        two_bad_incoming_edges = true;
                        break scc_nodes;
                    }
                }
            }
            if (two_bad_incoming_edges) {
                // sixth case
                return LocalComplexityValue.UNBOUNDED;
            } else {
                // seventh case

                LinkedHashSet<Node<CallArgument>> addBoundPreds = new LinkedHashSet<>();
                for (Node<CallArgument> alpha : addBoundNodes) {
                    addBoundPreds.addAll(graph.getIn(alpha));
                }

                LocalComplexityValue b_overline = LocalComplexityValue.POL0;

                for (Cycle<CallArgument> p : preds.get(scc)) {
                    if (SizeBoundComputation.intersects(p, addBoundPreds)) {
                        b_overline = b_overline.max(globalComplAkk.get(p));
                    }
                }

                ComplexityValue b_addConstantBound = ComplexityValue.constant();
                for (CallArgument alpha : scc.getNodeObjects()) {
                    LocalSizeBound lsb = alpha.getLocalSizeBound(aborter);
                    if (!LocalComplexityValue.ADDCONSTANTBOUND.equals(lsb.getC())) {
                        continue;
                    }
                    CpxIntTupleRule rho = alpha.rule;
                    b_addConstantBound = b_addConstantBound.max(K.get(rho));
                }

                ComplexityValue b_addBound = ComplexityValue.constant();
                for (CallArgument alpha : scc.getNodeObjects()) {
                    LocalSizeBound lsb = alpha.getLocalSizeBound(aborter);
                    if (!LocalComplexityValue.ADDBOUND.equals(lsb.getC())) {
                        continue;
                    }
                    CpxIntTupleRule rho = alpha.rule;
                    b_addBound = b_addBound.max(K.get(rho));
                }

                return LocalComplexityValue.ADDCONSTANTBOUND
                    .max(LocalComplexityValue.fromComplexityValue(b_addConstantBound))
                    .max(LocalComplexityValue.fromComplexityValue(b_addBound.mult(b_overline.getComplexityValue())))
                    .max(b_prime);
            }
        }

        throw new RuntimeException("should not happen");
    }

    // it still puzzles me that java collections don't have this
    private static <T> boolean intersects(Set<T> a, Set<T> b) {
        for (T i : a) {
            if (b.contains(i)) {
                return true;
            }
        }
        return false;
    }
}
