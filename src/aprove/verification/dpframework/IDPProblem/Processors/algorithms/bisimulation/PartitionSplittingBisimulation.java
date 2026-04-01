package aprove.verification.dpframework.IDPProblem.Processors.algorithms.bisimulation;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 *
 * @author Martin Pluecker
 */
public class PartitionSplittingBisimulation<T, E> implements IBisimulationAlgorithm<T, E> {

    @Override
    public Collection<Set<Node<T>>> getBisimulation(
            final SimpleGraph<T, Set<E>> graph,
            final Collection<Set<Node<T>>> initialPartition, final Abortion aborter)
            throws AbortionException {
        // hold partition calss for every Node<T>
        final Map<Node<T>, Set<Node<T>>> partitionMap = new LinkedHashMap<Node<T>, Set<Node<T>>>();
        for (final Set<Node<T>> partition : initialPartition) {
            for (final Node<T> n : partition) {
                partitionMap.put(n, partition);
            }
        }

        final Set<Set<Node<T>>> pOld = new LinkedHashSet<Set<Node<T>>>(initialPartition);
        Set<Set<Node<T>>> p = this.refine(initialPartition, partitionMap, graph.getNodes(), graph);
        while (!p.equals(pOld)) {
            aborter.checkAbortion();
            superB : for (final Set<Node<T>> superBlock : pOld) {
                if (p.contains(superBlock)) {
                    continue superB;
                }
                Set<Node<T>> smallestSubBlock = null;
                for (final Node<T> n : superBlock) {
                    final Set<Node<T>> subBlock = partitionMap.get(n);
                    if (smallestSubBlock == null || subBlock.size() < smallestSubBlock.size()) {
                        smallestSubBlock = subBlock;
                    }
                }
                if (smallestSubBlock != null) {
                    final Set<Node<T>> splitter1 = smallestSubBlock;
                    pOld.remove(superBlock);
                    superBlock.removeAll(smallestSubBlock);
                    final Set<Node<T>> splitter2 = superBlock;
                    pOld.add(splitter1);
                    pOld.add(splitter2);
                    p = this.refine(p, partitionMap, splitter1, splitter2, graph);
                    break superB;
                }
            }
        }
        return p;
    }

    /**
     * @param partitionMap the map is updated to reflect returned partition
     */
    protected Set<Set<Node<T>>> refine(final Collection<Set<Node<T>>> partition, final Map<Node<T>, Set<Node<T>>> partitionMap, final Set<Node<T>> splitter, final SimpleGraph<T, Set<E>> graph) {
        final Set<Set<Node<T>>> res = new LinkedHashSet<Set<Node<T>>>();

        final CollectionMap<E, Node<T>> preSplitter = new CollectionMap<E, Node<T>>();
        for (final Node<T> n : splitter) {
            for (final Edge<Set<E>, T> e : graph.getInEdges(n)) {
                for (final E edgeType : e.getObject()) {
                    preSplitter.add(edgeType, e.getStartNode());
                }
            }
        }

        for (final Set<Node<T>> block : partition) {
            if (preSplitter.isEmpty()) {
                res.add(block);
            } else {
                final Iterator<E> edgeTypeIterator = preSplitter.keySet().iterator();

                edgeTypeLoop : while (edgeTypeIterator.hasNext()) {
                    final Collection<Node<T>> preSet = preSplitter.get(edgeTypeIterator.next());

                    final Set<Node<T>> pre = new LinkedHashSet<Node<T>>();
                    final Set<Node<T>> nonPre = new LinkedHashSet<Node<T>>();
                    for (final Node<T> n : block) {
                        if (preSet.contains(n)) {
                            pre.add(n);
                            partitionMap.put(n, pre);
                        } else {
                            nonPre.add(n);
                            partitionMap.put(n, nonPre);
                        }
                    }

                    if ((!pre.isEmpty() && !nonPre.isEmpty()) || !edgeTypeIterator.hasNext()) {
                        if (!pre.isEmpty()) {
                            res.add(pre);
                        }

                        if (!nonPre.isEmpty()) {
                            res.add(nonPre);
                        }
                        break edgeTypeLoop;
                    }
                }
            }
        }
        return res;
    }

    /**
     * @param partitionMap the map is updated to reflect returned partition
     */
    protected Set<Set<Node<T>>> refine(final Collection<Set<Node<T>>> partition, final Map<Node<T>, Set<Node<T>>> partitionMap, final Set<Node<T>> splitter1, final Set<Node<T>> splitter2, final SimpleGraph<T, Set<E>> graph) {
        final Set<Set<Node<T>>> res = new LinkedHashSet<Set<Node<T>>>();
        final CollectionMap<E, Node<T>> preSplitter1 = new CollectionMap<E, Node<T>>();
        for (final Node<T> n : splitter1) {
            for (final Edge<Set<E>, T> e : graph.getInEdges(n)) {
                for (final E edgeType : e.getObject()) {
                    preSplitter1.add(edgeType, e.getStartNode());
                }
            }
        }

        final CollectionMap<E, Node<T>> preSplitter2 = new CollectionMap<E, Node<T>>();
        for (final Node<T> n : splitter2) {
            for (final Edge<Set<E>, T> e : graph.getInEdges(n)) {
                for (final E edgeType : e.getObject()) {
                    preSplitter2.add(edgeType, e.getStartNode());
                }
            }
        }

        final Set<E> edgeTypes = new LinkedHashSet<E>(preSplitter1.keySet());
        edgeTypes.addAll(preSplitter2.keySet());

        for (final Set<Node<T>> block : partition) {
            if (edgeTypes.isEmpty() || block.size() == 1) {
                res.add(block);
            } else {
                final Iterator<E> edgeTypeIterator = edgeTypes.iterator();

                edgeTypeLoop : while (edgeTypeIterator.hasNext()) {
                    final E edgeType = edgeTypeIterator.next();
                    final Collection<Node<T>> pre1Set = preSplitter1.get(edgeType);
                    final Collection<Node<T>> pre2Set = preSplitter2.get(edgeType);

                    final Set<Node<T>> pre12 = new LinkedHashSet<Node<T>>();
                    final Set<Node<T>> pre1 = new LinkedHashSet<Node<T>>();
                    final Set<Node<T>> pre2 = new LinkedHashSet<Node<T>>();
                    final Set<Node<T>> nonPre = new LinkedHashSet<Node<T>>();
                    for (final Node<T> n : block) {
                        if (pre1Set != null && pre1Set.contains(n)) {
                            if (pre2Set != null && pre2Set.contains(n)) {
                                pre12.add(n);
                                partitionMap.put(n, pre12);
                            } else {
                                pre1.add(n);
                                partitionMap.put(n, pre1);
                            }
                        } else if (pre2Set != null && pre2Set.contains(n)) {
                            pre2.add(n);
                            partitionMap.put(n, pre2);
                        } else {
                            nonPre.add(n);
                            partitionMap.put(n, nonPre);
                        }
                    }

                    int numOfBlocks = 0;
                    if (!pre1.isEmpty()) {
                        numOfBlocks ++;
                    }
                    if (!pre12.isEmpty()) {
                        numOfBlocks ++;
                    }
                    if (!pre2.isEmpty()) {
                        numOfBlocks ++;
                    }
                    if (!nonPre.isEmpty()) {
                        numOfBlocks ++;
                    }

                    if (numOfBlocks > 1) {
//                        if (block.iterator().next().getObject() instanceof BisimINode) {
//                            System.err.println("Splitting nodes");
//                        }

                        if (!pre1.isEmpty()) {
                            res.add(pre1);
                        }
                        if (!pre12.isEmpty()) {
                            res.add(pre12);
                        }
                        if (!pre2.isEmpty()) {
                            res.add(pre2);
                        }
                        if (!nonPre.isEmpty()) {
                            res.add(nonPre);
                        }
                        break edgeTypeLoop;
                    } else if (!edgeTypeIterator.hasNext()) {
                        res.add(block);
                    }
                }
            }
        }
        return res;
    }


}