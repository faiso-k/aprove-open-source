package aprove.input.Programs.llvm.segraph.edges;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Representation of edges noting a generalization step.
 * @author Marc Brockschmidt, cryingshadow
 */
public class LLVMGeneralizationInformation extends LLVMInstantiationInformation {

    /**
     * State with which we performed the generalization.
     */
    private final Node<LLVMAbstractState> generalizedWithNode;

    /**
     * @param node State with which we performed the generalization.
     * @param stateChanges Additional information which must hold while traversing the edge.
     * @param refMap map of refs in the source state of this edge to the corresponding refs in the target state.
     */
    public LLVMGeneralizationInformation(
        Node<LLVMAbstractState> node,
        Set<? extends LLVMRelation> stateChanges,
        Map<LLVMSimpleTerm, LLVMSimpleTerm> refMap
    ) {
        super(stateChanges, refMap);
        this.generalizedWithNode = node;
    }

    @Override
    public String getDotColor() {
        return "green";
    }

    @SuppressWarnings("unused")
    @Override
    public String getDotLabel() {
        final StringBuilder strBuilder = new StringBuilder();
        strBuilder.append("Generalization with ").append(this.generalizedWithNode.getNodeNumber());
        if (
            LLVMDebuggingFlags.ALWAYS_SHOW_NODE_USED_FOR_GENERALIZATION
            || LLVMDebuggingFlags.REMOVE_TOO_CONCRETE_PARTS_FROM_GRAPH
        ) {
            strBuilder.append(":\\n");
            strBuilder.append(this.generalizedWithNode.getObject().toDOTString());
        }
        this.getDotLabel(strBuilder);
        return strBuilder.toString();
    }

}
