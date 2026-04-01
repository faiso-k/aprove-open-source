package aprove.input.Programs.llvm.segraph.edges;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;

/**
 * Representation of edges noting a refinement step.
 * @author Marc Brockschmidt, cryingshadow
 */
public class LLVMRefinementInformation extends LLVMEdgeInformation {

//    /**
//     * The replacements in the internal LLVM structures instead of terms.
//     */
//    private final ImmutableMap<LLVMSymbolicVariable, LLVMSymbolicVariable> internalReplacements;
//
//    /**
//     * The replacements.
//     */
//    private final TRSSubstitution replacements;
//
//    /**
//     * The factory to build relations.
//     */
//    private final LLVMRelationFactory relationFactory;

    /**
     * @param changes The changes.
     * @param refReplacements The replacements.
     * @param relFactory The factory to build relations.
     */
    public LLVMRefinementInformation(Set<? extends LLVMRelation> changes) {
//        Map<LLVMSymbolicVariable, LLVMSymbolicVariable> refReplacements,
//        LLVMRelationFactory relFactory
//    ) {
        super(changes);
//        this.internalReplacements = ImmutableCreator.create(refReplacements);
//        this.relationFactory = relFactory;
//        TRSSubstitution s = TRSSubstitution.EMPTY_SUBSTITUTION;
//        for (Map.Entry<LLVMSymbolicVariable, LLVMSymbolicVariable> entry : refReplacements.entrySet()) {
//            s = s.extend(TRSSubstitution.create((TRSVariable) entry.getKey().toTerm(), entry.getValue().toTerm()));
//        }
//        this.replacements = s;
    }

//    @Override
//    public Triple<TRSFunctionApplication, TRSFunctionApplication, TRSTerm> applySubstitutionsToRuleTerms(
//        TRSFunctionApplication startNodeTerm,
//        TRSFunctionApplication endNodeTerm,
//        TRSTerm conditionTerm
//    ) {
//        TRSSubstitution varSubst = this.toSubstitution();
//         return new Triple<TRSFunctionApplication,TRSFunctionApplication,TRSTerm>(
//             startNodeTerm.applySubstitution(varSubst),
//             endNodeTerm,
//             conditionTerm.applySubstitution(varSubst)
//         );
//    }
//
//    @Override
//    public IntegerRelationSet getConstraints() {
//        IntegerRelationSet constraints = super.getConstraints();
//        for (Map.Entry<LLVMSymbolicVariable, LLVMSymbolicVariable> replacement : this.internalReplacements.entrySet()) {
//            constraints.add(this.relationFactory.equalTo(replacement.getKey(), replacement.getValue()));
//        }
//        return constraints;
//    }
//
    @Override
    public String getDotColor() {
        return "orange";
    }

    @Override
    public String getDotLabel() {
        StringBuilder strBuilder = new StringBuilder();
        strBuilder.append("Refinement");
        this.getDotLabel(strBuilder);
        return strBuilder.toString();
    }

//    /**
//     * @return The replacements as map from references to references.
//     */
//    public ImmutableMap<LLVMSymbolicVariable, LLVMSymbolicVariable> getReplacements() {
//        return this.internalReplacements;
//    }
//
//    /**
//     * @return A substitution of references in the source state which have been replaced by other references in the
//     *         target state.
//     */
//    public TRSSubstitution toSubstitution() {
//        return this.replacements;
//    }

}
