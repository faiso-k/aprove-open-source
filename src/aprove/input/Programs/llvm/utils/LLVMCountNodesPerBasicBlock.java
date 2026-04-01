package aprove.input.Programs.llvm.utils;

import java.util.*;
import java.util.Map.*;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LLVMCountNodesPerBasicBlock {
	
	private static class CountInfo {
		int total = 0;
		int withEvalEdge = 0;
		int withCallAbstrEdge = 0;
		int withRefinemenEdget = 0;
		int withSkipEdge =  0;
		int withGenEdge = 0;
	}

	public static Map<List<LLVMProgramPosition>,CountInfo> getNodeCountPerBlock(LLVMSEGraph graph) {
		Map<List<LLVMProgramPosition>,CountInfo> unsorted = new LinkedHashMap<>();
		
		Set<Node<LLVMAbstractState>> nodes = graph.getNodes();
		
		for(Node<LLVMAbstractState> node : nodes) {
			LLVMAbstractState state = node.getObject();
			
			List<LLVMProgramPosition> stack;
			LLVMProgramPosition progPos = state.getProgramPosition();
			
			if(progPos.getLine() != 0) {
				continue;
				//we are only interested in those states at the beginning of a block in their topmost stack frame
			}
			
			/*if(graph.getOutEdges(node).stream().anyMatch(e -> e.getObject() instanceof LLVMInstantiationInformation)) {
				continue;
				//nodes with outgoing gen edges are boring
			}*/
			
			if(state.getCallStack().isEmpty()) {
				stack = Collections.singletonList(progPos);
			} else {
				stack = new LinkedList<>();
				stack.add(progPos);
				
				Iterator<LLVMReturnInformation> stackIt = state.getCallStack().iterator();
				while(stackIt.hasNext()) {
					stack.add(stackIt.next().getProgPos());
				}
				
			}
			
			CountInfo currentCounts = unsorted.computeIfAbsent(stack, k -> new CountInfo());
			
			currentCounts.total++;
			for(Edge<LLVMEdgeInformation,LLVMAbstractState> e: graph.getOutEdges(node)) {
				LLVMEdgeInformation edge = e.getObject();
				if(edge instanceof LLVMEvaluationInformation) {
					currentCounts.withEvalEdge++;
				} else if(edge instanceof LLVMInstantiationInformation) {
					currentCounts.withGenEdge++;
				} else if(edge instanceof LLVMRefinementInformation) {
					currentCounts.withRefinemenEdget++;
				} else if(edge instanceof LLVMCallAbstractionEdge) {
					currentCounts.withCallAbstrEdge++;
				}
				
			}
			
			
		}
		
		return unsorted;
	}
	
	public static void printSortedCountPerBlock(LLVMSEGraph graph) {
		Map<List<LLVMProgramPosition>,CountInfo> unsortedMap = getNodeCountPerBlock(graph);
		
		List<Map.Entry<List<LLVMProgramPosition>,CountInfo>> asList = new ArrayList<>(unsortedMap.entrySet());
		
		Collections.sort(asList, new Comparator<Map.Entry<List<LLVMProgramPosition>,CountInfo>>() {

			@Override
			public int compare(Entry<List<LLVMProgramPosition>, CountInfo> arg0,
					Entry<List<LLVMProgramPosition>, CountInfo> arg1) {
				return arg0.getValue().total - arg1.getValue().total;
			}

        });
		
		for(Map.Entry<List<LLVMProgramPosition>,CountInfo> e : asList) {
			CountInfo counts = e.getValue();
			System.err.println(stackListToString(e.getKey()) + ": " + counts.total + 
					"(eval: " + counts.withEvalEdge +", inst/gen: " + counts.withGenEdge +", refi: " + counts.withRefinemenEdget +", skip: " + counts.withSkipEdge  + ", call abstr: " + counts.withCallAbstrEdge +")");
		}
	}
	
	private static String stackListToString(List<LLVMProgramPosition> stack) {
		StringBuffer sb = new StringBuffer();
		for(LLVMProgramPosition pp : stack) {
			sb.append("[" + pp.getFunction() + "," + pp.getBlock()+"]");
		}
		return sb.toString();
	}
}
