package aprove.input.Programs.llvm.segraph.edges;

import java.util.Collections;
import java.util.Set;

import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Shows that a intersection failed in the graph. This means that an intersection evoked an inconsistent state.
 * The end must be a return node, just to show it.
 * @author Frank
 */
public class LLVMFunctionSkipFailureEdge extends LLVMEdgeInformation {

    public LLVMFunctionSkipFailureEdge(Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> returnNode, Set<LLVMSEPath> executionPaths, Set<LLVMSEPath> cycles) {
    	super(Collections.emptySet());
        this.returnNode = returnNode;
        this.callNode = callNode;
        this.executionPaths = executionPaths;
        this.cycles = cycles;
    }

    //note that this is the return node the intersection failed with,
    //not the copy of that return node which this edge points to.
    public Node<LLVMAbstractState> getReturnNode() {
        return this.returnNode;
    }
    
    public Node<LLVMAbstractState> getCallNode() {
        return this.callNode;
    }
    
    public Set<LLVMSEPath> getRespectedPaths() {
    	return this.executionPaths;
    }

    public Set<LLVMSEPath> getRespectedCycles() {
        return this.cycles;
    }


    private final Node<LLVMAbstractState> callNode;
    
    private final Node<LLVMAbstractState> returnNode;
    
    private final Set<LLVMSEPath> executionPaths;

    private final Set<LLVMSEPath> cycles;


    @Override
    //TODO update
    public String getDotLabel() {
        final StringBuilder strBuilder = new StringBuilder();
        strBuilder.append("DEBUG EGDGE:\nFailed to skip  via\n return node "  + this.returnNode.getNodeNumber() + "\nrespected paths:\n");
        if(executionPaths != null) {
	        for(LLVMSEPath path : executionPaths) {
	        	strBuilder.append(path.toString() + "\n");
	        }
        }
        this.getDotLabel(strBuilder);
        return strBuilder.toString();
    }

    @Override
    public String getDotColor() {
        return "red";
    }
	
	@Override
	public TRSTerm toTerm() {
		return LLVMRelationUtils.toTerm(Collections.emptySet());
	}

}
