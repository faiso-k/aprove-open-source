package aprove.input.Programs.llvm.segraph.edges;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Indicates that we "skipped" a (recursive) function, connecting the start of the function with its return
 * @author Frank
 */
public class LLVMMethodSkipEdge extends LLVMEdgeInformation {

    private final LLVMIntersectionResult intersectionResult;



	public LLVMMethodSkipEdge(
			LLVMIntersectionResult intersectionResult
    ) {
        super(new LinkedHashSet<LLVMRelation>());
        this.intersectionResult = intersectionResult;
    }


    @Override
    public String getDotColor() {
        return "\"#ff00ff\"";
    }

    @Override
    public String getDotLabel() {
        final StringBuilder strBuilder = new StringBuilder();
        //FIXME
        strBuilder.append("Method Skip "
        		+ "\\nvia node " + getEndNode().getNodeNumber() 
        		+ "\\nrespected " + intersectionResult.getRespectedExecutionPaths().size() + " paths:\\n");
        /*for(LLVMSEPath path : intersectionResult.getRespectedExecutionPaths()) {
        	strBuilder.append(path.toString() + "\\n");
        }
        strBuilder.append("respected cycles:\\n");
        for(LLVMSEPath cycle : intersectionResult.getRespectedCycles()) {
        	strBuilder.append(cycle.toString() + "\\n");
        }*/
        
        /*strBuilder.append("Variable Mappings:\n");
        for(LLVMSymbolicVariable key : intersectionResult.getRenamingsOnPathsFromCallToReturnState().keySet()) {
        	strBuilder.append(key + ":" + intersectionResult.getRenamingsOnPathsFromCallToReturnState().get(key) + "\n");
        }
        strBuilder.append("Non-Deallocated Malloc allocations:\n");
        strBuilder.append(intersectionResult.getPreserverdMallocAllocationsOfCallState() + "\n");
        
        strBuilder.append("Unchanged Heap Ranges:\n");
        strBuilder.append(intersectionResult.getPreserverdCallStateHeapEntrieRanges() + "\n");
        
        this.getDotLabel(strBuilder);*/
        return strBuilder.toString();
    }

    public Node<LLVMAbstractState> getEndNode() {
        return intersectionResult.getReturnNode();
    }
    
    @Deprecated
    public LLVMIntermediateIntersectionResult getIntersectionResultOld() {
    	return intersectionResult.getLegacyResult();
	}
    

    public LLVMIntersectionResult getIntersectionResult() {
    	return intersectionResult;
    }


}
