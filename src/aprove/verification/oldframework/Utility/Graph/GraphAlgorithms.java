package aprove.verification.oldframework.Utility.Graph;

import java.util.*;

import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Generic graph algorithms
 */
public class GraphAlgorithms {

    /**
     * Remove all nodes from the graph from which no cycles are reachable
     */
    public static <T> Set<Node<T>> removeTrailingNodes(SimpleGraph<T, ?> graph) {
        ArrayList<Cycle<T>> sccList =
            new ArrayList<Cycle<T>>(graph.getSCCs(false));
        Set<Node<T>> cycleFollows = new HashSet<Node<T>>();
        Set<Node<T>> trailingNodes = new HashSet<Node<T>>();
        for (Cycle<T> scc : sccList) {
            if (scc.size() > 1) {
                cycleFollows.addAll(scc);
            } else {
                Node<T> node = scc.iterator().next();
                Set<Node<T>> outNodes = graph.getOut(node);
                /* This works as graph.getSCCs() returns the nodes in reverse
                 * topological order: If a node is followed by a SCC, this
                 * SCC is visited therefore and hence its nodes are in
                 * cycleFollows. */
                if (outNodes.contains(node)
                        || !Collections.disjoint(outNodes, cycleFollows)) {
                    cycleFollows.add(node);
                } else {
                    trailingNodes.add(node);
                }
            }
        }

        for (Node<T> node : trailingNodes) {
            graph.removeNode(node);
        }
        return trailingNodes;
    }
    
    
    /**
     * 
     * @return A list of all cycles (i.e., cyclic paths without vertex repetition) in graph.
     * The result list does not contain duplicates (i.e., permutations of the same cycle)
     */
    public static <T,E> List<ArrayList<Node<T>>> getCycles(SimpleGraph<T,E> graph, EdgeFilter<E,T> filter) {
    	return new JohnsonsCycleAlgorithm<T,E>().getCycles(graph,filter);
    }
    
    /**
     * Implementation of Johnson's Algorithm for determining all cycles (i.e., cyclic paths without vertex repetition).
     * See paper "FINDING ALL THE ELEMENTARY CIRCUITS OF A DIRECTED GRAPH" by DONALD B. JOHNSON
     */
    private static class JohnsonsCycleAlgorithm<T,E> {
    	LinkedHashSet<Node<T>> blocked;
    	
    	//Corresponds to the data structure of the same name in the algorithm spec
    	LinkedHashMap<Node<T>,LinkedHashSet<Node<T>>> B;
    	
    	ArrayList<Node<T>> allNodes;
    	Map<Integer,Node<T>> indexToNode;
    	Deque<Node<T>> stack;
    	
    	List<ArrayList<Node<T>>> foundCycles;
    	
    	private void unblock(Node<T> node) {
    		blocked.remove(node);
    		LinkedHashSet<Node<T>> curB = B.get(node);
    		
    		Iterator<Node<T>> bIterator = curB.iterator();
    		while(bIterator.hasNext()) {
    			Node<T> w = bIterator.next();
    			bIterator.remove();
    			
    			if(blocked.contains(w)) {
    				unblock(w);
    			}
    		}
    		
    	}
    	
    	/**
    	 * Recursively tries to build a circuit from s to s.
    	 * Corresponds to the function of the same name in the algorithm paper
    	 * 
    	 * @param v the current node
    	 * @param s
    	 * @param currentSCCNodes the set of nodes that denote the current SCC
    	 * @return whether we finished a cycle or not
    	 */
    	private boolean circuit(Node<T> v,Node<T> s,
								LinkedHashSet<Node<T>> currentSCCNodes,
								SimpleGraph<T,E> subgraphContainingSCC,
								EdgeFilter<E,T> filter) {
    		boolean finishedCycle = false;
    		
    		stack.addLast(v);
    		blocked.add(v);
    		
    		for(Node<T> successor: subgraphContainingSCC.getOut(v)) {
    			//Pretend that we are only considered the subgraph induced by currentSCCNodes
    			if(currentSCCNodes.contains(successor)) {
    				if(successor == s) {
    					ArrayList<Node<T>> newFoundCycle = new  ArrayList<>(stack);
    					newFoundCycle.add(s);
    					foundCycles.add(newFoundCycle);
    					finishedCycle = true;
    				} else if(!blocked.contains(successor)) {
    					finishedCycle |= circuit(successor, s, currentSCCNodes,subgraphContainingSCC, filter);
    				}
    			}
    		}
    		if(finishedCycle) {
    			unblock(v);
    		} else {
    			for(Edge<E,T> outEdge : subgraphContainingSCC.getOutEdges(v)) {
    				if(!filter.selectEdge(outEdge.getStartNode(),outEdge.getEndNode(),outEdge.getObject())) {
    					continue;
					}

    				//Pretend that we are only considered the subgraph induced by currentSCCNodes
    				if(currentSCCNodes.contains(outEdge)) {
    					B.get(outEdge).add(v);
    				}
    				
    			}
    		}
    		
    		stack.removeLast();
    		return finishedCycle;
    		
    	}
    	
    	
    	/**
    	 * 
    	 * @param remainingSCCs A set of SCCs
    	 * @return a pair <x,y> such that x is the SCC from remainingSCCs which contains the node with the smallest index. x is null iff remainingSCCs is empty 
    	 */
    	private Pair<Cycle<T>,Integer> getLeastSCC(LinkedHashSet<Cycle<T>> remainingSCCs) {
			int minID = -1;
			Cycle<T> minSCC = null;

			for (Cycle<T> curSCC : remainingSCCs) {
				for (Node<T> curSCCNode : curSCC) {
					if (minSCC == null || curSCCNode.getNodeNumber()< minID) {
						minID = curSCCNode.getNodeNumber();
						minSCC = curSCC;
					}
				}

			}
			return new Pair<>(minSCC, minID);
		}
    	
    	/**
    	 * Main procedure, as in the paper
    	 */
    	List<ArrayList<Node<T>>> getCycles(SimpleGraph<T,E> graph, EdgeFilter<E,T> filter) {
    		//graphNodesToIndex = new LinkedHashMap<>();
    		indexToNode = new LinkedHashMap<>();
    		
    		
    		allNodes = new ArrayList<>();
    		foundCycles = new ArrayList<>();
    		B = new LinkedHashMap<>();
    		stack = new ArrayDeque<>();
			blocked = new LinkedHashSet<>();
    		

    		for(Node<T> graphNode : graph.getNodes()) {
    			//graphNodesToIndex.put(graphNode,nodeID++);
    			indexToNode.put(graphNode.getNodeNumber(), graphNode);
    			allNodes.add(graphNode);
    			B.put(graphNode, new LinkedHashSet<>());
    		}
    		
    		
    		
    		LinkedHashSet<Node<T>> remainingNodes = new LinkedHashSet<>(allNodes);
    		LinkedHashSet<Cycle<T>> remainingSCCs = graph.getSCCs(filter);
    		SimpleGraph<T,E> remainingSubgraph = graph;
    		int curNodeID = 0;
    		
    		
			while (!remainingSCCs.isEmpty() && curNodeID < allNodes.size() - 1) {
				Pair<Cycle<T>, Integer> minSCCAndID = getLeastSCC(remainingSCCs);
				Cycle<T> minSCC = minSCCAndID.x;

				int minNodeID = minSCCAndID.y;
				Node<T> minNode = indexToNode.get(minNodeID);

				// The original algorithm only unblocks nodes from minSCC, but
				// the other ones are not accessed any more
				blocked.clear();
				for (Node<T> curSCCNode : minSCC) {
					B.get(curSCCNode).clear();
				}

				circuit(minNode, minNode, minSCC,remainingSubgraph,filter);

				for (int obsoleteNodeID = curNodeID; obsoleteNodeID <= minNodeID; obsoleteNodeID++) {
					remainingNodes.remove(indexToNode.get(obsoleteNodeID));
				}
				// Creates induced subgraph
				remainingSubgraph = new SimpleGraph<>(remainingNodes, remainingSubgraph);
				remainingSCCs = remainingSubgraph.getSCCs(filter);

				curNodeID = minNodeID + 1;

			}
    		
    		return foundCycles;
    	}
    	
    }
    


}
