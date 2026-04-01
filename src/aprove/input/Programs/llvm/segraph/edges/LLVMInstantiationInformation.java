package aprove.input.Programs.llvm.segraph.edges;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Representation of edges noting an instantiation step.
 * @author Marc Brockschmidt, cryingshadow
 */
public class LLVMInstantiationInformation extends LLVMEdgeInformation {

    /**
     * A mapping of refs in the target state of this edge to the corresponding refs in the source state.
     */
    private final Map<LLVMSimpleTerm, LLVMSimpleTerm> referenceCorrespondenceMap;

    /**
     * @param stateChanges Additional information which must hold while traversing the edge.
     * @param refMap Map of refs in the target state of this edge to the corresponding refs in the source state.
     */
    public LLVMInstantiationInformation(
        Set<? extends LLVMRelation> stateChanges,
        Map<LLVMSimpleTerm, LLVMSimpleTerm> refMap
    ) {
        super(stateChanges);
        this.referenceCorrespondenceMap = refMap;
    }

    @Override
    public String getDotColor() {
        return "blue";
    }

//    @Override
//    public Triple<TRSFunctionApplication, TRSFunctionApplication, TRSTerm> applySubstitutionsToRuleTerms(
//        TRSFunctionApplication startNodeTerm,
//        TRSFunctionApplication endNodeTerm,
//        TRSTerm conditionTerm
//    ) {
//        TRSSubstitution varSubst = this.toSubstitution();
//         return
//             new Triple<TRSFunctionApplication, TRSFunctionApplication, TRSTerm>(
//                 startNodeTerm,
//                 endNodeTerm.applySubstitution(varSubst),
//                 conditionTerm.applySubstitution(varSubst)
//             );
//    }

//    /**
//     * @see aprove.input.Programs.llvm.segraph.edges.LLVMEdgeInformation#getConstraints()
//     * In the case of an instance edge, a model satisfying the constraints
//     * represents not a pair of states but a single concrete state
//     * that is an instance of both abstract states at the ends of the edge
//     */
//    @Override
//    public IntegerRelationSet getConstraints() {
//        IntegerRelationSet constraints = super.getConstraints();
//        for (Map.Entry<LLVMSymbolicVariable, LLVMSymbolicVariable> equiv :
//            this.referenceCorrespondenceMap.entrySet()
//        ) {
//            constraints.add(
//                LLVMDefaultRelationFactory.LLVM_DEFAULT_RELATION_FACTORY.equalTo(equiv.getKey(), equiv.getValue())
//            );
//        }
//        return constraints;
//    }

    @Override
    public String getDotLabel() {
        StringBuilder strBuilder = new StringBuilder();
        strBuilder.append("Instance ");
        this.getDotLabel(strBuilder);
        return strBuilder.toString();
    }

    /**
     * @return a copy of the reference map
     */
    public Map<LLVMSimpleTerm, LLVMSimpleTerm> getReferenceCorrespondenceMap() {
        return new LinkedHashMap<>(this.referenceCorrespondenceMap);
    }

    /**
     * @return The instance mapping as substitution.
     */
    public Substitution toSubstitution() {
        Map<TRSVariable, TRSTerm> res = new LinkedHashMap<TRSVariable, TRSTerm>();
        for (Map.Entry<LLVMSimpleTerm, LLVMSimpleTerm> entry : this.getReferenceCorrespondenceMap().entrySet()) {
            if (!(entry.getKey() instanceof LLVMConstant)) {
                res.put((TRSVariable)entry.getKey().toTerm(), entry.getValue().toTerm());
            }
        }
        return Substitution.toSubstitution(res);
    }

//    @Override
//    public TRSTerm toRuleCondition(boolean useInvariantsOnInstanceEdges) {
//        if (useInvariantsOnInstanceEdges) {
//            return super.toRuleCondition(useInvariantsOnInstanceEdges);
//        } else {
//            return TRSTerm.createFunctionApplication(IDPPredefinedMap.DEFAULT_MAP.getBooleanTrue().getSym());
//        }
//    }

//    /**
//     * @return A substitution mapping variables in the more abstract target state to their more concrete counterparts
//     *         in the more concrete state.
//     */
//    public TRSSubstitution toSubstitution() {
//        TRSSubstitution res = TRSSubstitution.EMPTY_SUBSTITUTION;
//        for (Map.Entry<LLVMSymbolicVariable, LLVMSymbolicVariable> e : this.referenceCorrespondenceMap.entrySet()) {
//            LLVMSymbolicVariable ref1 = e.getKey();
//            LLVMSymbolicVariable ref2 = e.getValue();
//            if (ref1 instanceof LLVMHeuristicVariable && ((LLVMHeuristicVariable)ref1).isConcrete()) {
//                if (Globals.useAssertions) {
//                    assert (((LLVMHeuristicVariable)ref2).isConcrete()) : "Instantiated constant by a non-constant...";
//                    assert (
//                        ((LLVMHeuristicConstRef)ref1).getIntegerValue().equals(
//                            ((LLVMHeuristicConstRef)ref2).getIntegerValue()
//                        )
//                    ) : "Instantiated two different constants...";
//                }
//            } else {
//                res = res.extend(TRSSubstitution.create((TRSVariable)ref1.toTerm(), ref2.toTerm()));
//            }
//        }
//        return res;
//    }

//    @Override
//    protected void getDotLabel(StringBuilder strBuilder) {
//        strBuilder.append(this.referenceCorrespondenceMap);
//        super.getDotLabel(strBuilder);
//    }

}
