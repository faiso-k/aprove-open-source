package aprove.input.Programs.llvm.utils;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * This class "compacts" an LLVMSEGraph by cutting some nodes out of the SEGraph:
 * Given a oath of states of the form s_0 -> s_1 -> ... ->  s_{n-1} -> s_n where all states s_i with i \in [1,n-1] have only one incoming and
 * one outgoing edge, we replace the path above by a single edge s_0 -> s_n. The edge between those to states is a special one, telling us what we have done  
 * 
 * @author Frank
 *
 */
public class LLVMSEGraphOutputCompactor {
	
	public static String[]  PROGRAM_POSITIONS_NOT_TO_CLEAR_CONTENTS_OF = {
			"(test, 20, 0)"
	};
	
	public static boolean CLEAR_INTERMEDIATE_STATE_CONTENTS = true;
	
	public static boolean SHOW_INDIVIDUAL_STEPS_ON_EDGES = false;
	
	public static boolean SHOW_INSTRUCTION_COUNTS = false;
	
	public static boolean KEEP_ENTRY_STATES = true;
	
	public static boolean KEEP_RETURN_STATES = true;
	
	public static boolean KEEP_CALL_STATES = true;
	
	public static boolean COMPACT_PATHS = false;
	
	//public static boolean 
	
	public static LLVMSEGraph  compactGraphForOutput(LLVMSEGraph originalGraph) {
		return new LLVMSEGraphOutputCompactor(originalGraph).compact();
	}
	
	private LLVMSEGraphOutputCompactor(LLVMSEGraph originalGraph) {
		originalNodesToSimplification = new LinkedHashMap<>();
		this.originalGraph = originalGraph;
	}
	
	Map<Node<LLVMAbstractState>,Node<LLVMAbstractState>> originalNodesToSimplification;
	LLVMSEGraph originalGraph;
	Set<String> programPositionsNotToSimplify = new LinkedHashSet<>(Arrays.asList(PROGRAM_POSITIONS_NOT_TO_CLEAR_CONTENTS_OF));
	
	private Node<LLVMAbstractState> getSimplification(Node<LLVMAbstractState> originalGraphNode) {
		return originalNodesToSimplification.computeIfAbsent(originalGraphNode, n -> simplify(n));
	}

	private  LLVMSEGraph  compact() {
		LLVMSEGraph compactedGraph = new LLVMSEGraph(originalGraph.getModule(), null, originalGraph.getStrategyParameters(), null);
		LLVMIntersectionHeuristics heuristics = originalGraph.getIntersectionHeuristics();
		
		compactedGraph.setRoot(originalGraph.getRoot());
		
		
		final Set<Node<LLVMAbstractState>> seen = new LinkedHashSet<Node<LLVMAbstractState>>();
        final Stack<Node<LLVMAbstractState>> todo = new Stack<>();
        
        todo.addAll(originalGraph.getNodes()
        		.parallelStream()
        		.filter(n -> originalGraph.getIn(n).isEmpty())
        		.collect(Collectors.toSet()));
        
        todo.forEach(n -> compactedGraph.addNode(getSimplification(n)));
        
        
        while (!todo.isEmpty()) {
        	Node<LLVMAbstractState> todoNode = todo.pop();
        	
        	
            Node<LLVMAbstractState> curNode = todoNode;
            Set<Node<LLVMAbstractState>> successors = originalGraph.getOut(curNode);
            List<Edge<LLVMEdgeInformation,LLVMAbstractState>> linearPath = new LinkedList<>();
            
            while(successors.size() == 1 && COMPACT_PATHS) {
            	Node<LLVMAbstractState> singleSuccesor = successors.iterator().next();
            	
            	LLVMAbstractState successorState = singleSuccesor.getObject();
            	if(KEEP_CALL_STATES && heuristics.isCallState(successorState)) {
            		break;
            	}
            	
            	if(KEEP_ENTRY_STATES && heuristics.isCallAbstractionOrEntryState(successorState)) {
            		break;
            	}
            	
            	if(KEEP_RETURN_STATES && heuristics.isReturnState(successorState)) {
            		break;
            	}
            	
            	
            	linearPath.add(originalGraph.getEdge(curNode, singleSuccesor));
            	curNode = singleSuccesor;
            	successors = originalGraph.getOut(curNode);
            }
            
            if(!linearPath.isEmpty()) {
            	Set<Map<Pair<String,String>,Integer>> basicBlockCountsForPaths = null;
            	if(originalGraph.getOut(curNode).isEmpty()) {
            		basicBlockCountsForPaths = getExecutionCountForBasicBlocks(originalGraph,curNode);
            	}
            	compactedGraph.addEdge(getSimplification(todoNode),getSimplification(curNode),new LLVMCompactedOutputEdge(linearPath,basicBlockCountsForPaths));
            }
            
            
            
            for (final Node<LLVMAbstractState> succ : successors) {
            	compactedGraph.addEdge(getSimplification(curNode),getSimplification(succ),originalGraph.getEdgeObject(curNode, succ));
                if (seen.add(succ)) {
                    todo.push(succ);
                }
            }

        }
        
        
		if(Globals.useAssertions) {
			
			if (!CLEAR_INTERMEDIATE_STATE_CONTENTS) {
				Set<Edge<LLVMEdgeInformation, LLVMAbstractState>> edgeDelta = new LinkedHashSet<>(
						originalGraph.getEdges());
				edgeDelta.removeAll(compactedGraph.getEdges());
				for (Edge<LLVMEdgeInformation, LLVMAbstractState> deltaEdge : edgeDelta) {
					assert originalGraph.getOut(deltaEdge.getStartNode()).size() == 1;
				}
			}
			
			for(Node<LLVMAbstractState> node : originalGraph.getNodes()) {
				if(originalGraph.getOut(node).isEmpty()) {
					assert compactedGraph.contains(node);
				}
			}
		}
		
		return compactedGraph;
	}
	
	
	private Node<LLVMAbstractState> simplify(Node<LLVMAbstractState> node) {
		LLVMAbstractState oldState = node.getObject();
		if(CLEAR_INTERMEDIATE_STATE_CONTENTS 
				&& !originalGraph.getIn(node).isEmpty()
				&& !originalGraph.getOut(node).isEmpty()
				&& node != originalGraph.getRoot()
				&& !programPositionsNotToSimplify.contains(oldState.getProgramPosition().toString())) {
				
			LLVMAbstractState newState = oldState.clearKnowledge(null);
			//newState.set
			return new Node<>(newState);
			
		} else {
			return node;
		}
	}
	
	private static Set<Map<Pair<String,String>,Integer>> getExecutionCountForBasicBlocks(LLVMSEGraph originalGraph, Node<LLVMAbstractState> node) {
		Set<Map<Pair<String,String>,Integer>> res = new LinkedHashSet<>();
		
		Set<List<Node<LLVMAbstractState>>> allPaths = originalGraph.getAllPaths(originalGraph.getRoot(), node);
		
		for(List<Node<LLVMAbstractState>> path : allPaths) {
			Map<Pair<String,String>,Integer> basicBlocksToCounts = new LinkedHashMap<>();
			
			Node<LLVMAbstractState> prevNode = null;
			
			for(Node<LLVMAbstractState> curNode : path) {
				LLVMAbstractState state = curNode.getObject();
				
				LLVMProgramPosition progPos = state.getProgramPosition();
				LLVMEdgeInformation edge = prevNode == null ? null : originalGraph.getEdgeObject(prevNode, curNode);
				
				if(progPos.getLine() == 0 && edge instanceof LLVMEdgeInformation) {
					//at start of block
					
					String function = progPos.getFunction();
					String basicBlock = progPos.getBlock();
					
					Pair<String,String> key = new Pair<>(function,basicBlock);
					
					int count = basicBlocksToCounts.getOrDefault(key, 0);
					
					basicBlocksToCounts.put(key,count+1);
					
				}
				prevNode = curNode;
			}
			
			
			res.add(basicBlocksToCounts);
		}
		
		return res;
		
	}
	
	
}
