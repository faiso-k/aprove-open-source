package aprove.input.Programs.llvm.segraph.edges;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * This edge is used to indicate that we compated some edges from the SEGraph into one before printing the graph
 * THIS IS ONLY FOR GRAPHICAL OUTPUT, IT MUST NEVER OCCUR IN A GRAPH THAT IS ACUTALLY WORKED ON!
 * @author Frank
 *
 */
public class LLVMCompactedOutputEdge extends LLVMEdgeInformation {
	

	public LLVMCompactedOutputEdge(List<Edge<LLVMEdgeInformation,LLVMAbstractState>> originalEdges, 
			Set<Map<Pair<String,String>,Integer>> basicBlockExecutionCountsForPaths) {
		super(Collections.emptySet());
		this.originalEdges = originalEdges;
		this.basicBlockExecutionCountsForPaths = basicBlockExecutionCountsForPaths;
	}

	List<Edge<LLVMEdgeInformation,LLVMAbstractState>> originalEdges;
	
	//can be null
	Set<Map<Pair<String,String>,Integer>> basicBlockExecutionCountsForPaths;

	@Override
	public String getDotColor() {
		return "orange";
	}

	@Override
	public String getDotLabel() {
		StringBuffer sb = new StringBuffer();
		
		if(LLVMSEGraphOutputCompactor.SHOW_INDIVIDUAL_STEPS_ON_EDGES) {
			originalEdges.forEach(e -> sb.append(
					e.getObject().getClass().getSimpleName() + " " + e.getEndNode().getObject().getProgramPosition().toString() + "\n"));
		
		}
		
		if(LLVMSEGraphOutputCompactor.SHOW_INSTRUCTION_COUNTS && basicBlockExecutionCountsForPaths != null) {
			int pathcount = 0;
			for(Map<Pair<String,String>,Integer> mapForCertainPath : basicBlockExecutionCountsForPaths) {
				sb.append("\nPath No " + pathcount + ":\n");
				
				for(Map.Entry<Pair<String,String>, Integer> e : mapForCertainPath.entrySet()) {
					if(e.getValue() > 1) {
						sb.append(e.getKey().x + "," + e.getKey().y + ": " + e.getValue() + "\n");
					}
					
				}
				
				
			}
			pathcount++;
		}
		
		return sb.toString();
	}
	
}
