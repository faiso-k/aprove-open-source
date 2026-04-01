package aprove.input.Programs.llvm.segraph.edges;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;

/**
 * Representation of edges noting an evaluation step.
 * @author Marc Brockschmidt, cryingshadow
 */
public class LLVMEvaluationInformation extends LLVMEdgeInformation {

    /**
     * @param stateChanges A collection of changes between the source and target of this edge.
     */
    public LLVMEvaluationInformation(Set<? extends LLVMRelation> stateChanges) {
        super(stateChanges);
    }

//    @Override
//    public Triple<TRSFunctionApplication, TRSFunctionApplication, TRSTerm> applySubstitutionsToRuleTerms(
//        TRSFunctionApplication startNodeTerm,
//        TRSFunctionApplication endNodeTerm,
//        TRSTerm conditionTerm
//    ) {
//        TRSTerm currentConditionTerm = conditionTerm;
//        TRSFunctionApplication currentEndNodeTerm = endNodeTerm;
//        Set<LLVMStateChangeInformation> changesOnEdge = this.getChangesOnEdge();
//        for (LLVMStateChangeInformation state_change : changesOnEdge) {
//            if (state_change instanceof LLVMRelation) {
//                LLVMRelation rel = ((LLVMRelation)state_change);
//                if (rel.isEquation() && rel.getLhs() instanceof LLVMHeuristicVarRef) {
//                    TRSVariable lhs = (TRSVariable)rel.getLhs().toTerm();
//                    if (!startNodeTerm.getArguments().contains(lhs)) {
//                        Substitution subst = TRSSubstitution.create(lhs, rel.getRhs().toTerm());
//                        currentConditionTerm = currentConditionTerm.applySubstitution(subst);
//                        currentEndNodeTerm = currentEndNodeTerm.applySubstitution(subst);
//                    }
//                }
//            }
//        }
//         return
//             new Triple<TRSFunctionApplication, TRSFunctionApplication, TRSTerm>(
//                 startNodeTerm,
//                 currentEndNodeTerm,
//                 currentConditionTerm
//             );
//    }

    @Override
    public String getDotColor() {
        return "black";
    }

    @Override
    public String getDotLabel() {
        final StringBuilder strBuilder = new StringBuilder();
        strBuilder.append("Eval");
        this.getDotLabel(strBuilder);
        return strBuilder.toString();
    }

}
