package aprove.input.Programs.llvm.segraph.edges;

import java.util.*;

/**
 * Indicates that we omitted all but the topmost stack frame (for recursion)
 * @author Frank
 */
public class LLVMCallAbstractionEdge extends LLVMEdgeInformation {

    /**
     * Creates an edge with empty change information.
     */
    public LLVMCallAbstractionEdge() {
        super(Collections.emptySet());
    }

//    @Override
//    public Triple<TRSFunctionApplication, TRSFunctionApplication, TRSTerm>
//            applySubstitutionsToRuleTerms(TRSFunctionApplication startNodeTerm,
//                                          TRSFunctionApplication endNodeTerm,
//                                          TRSTerm conditionTerm) {
//        // TODO This is just a stub
//        return new Triple<>(startNodeTerm,endNodeTerm,conditionTerm);
//    }

    @Override
    public String getDotColor() {
        // TODO Auto-generated method stub
        return "\"#00ffff\"";
    }

    @Override
    public String getDotLabel() {
        final StringBuilder strBuilder = new StringBuilder();
        strBuilder.append("Call Abstraction");
        this.getDotLabel(strBuilder);
        return strBuilder.toString();
    }

}
