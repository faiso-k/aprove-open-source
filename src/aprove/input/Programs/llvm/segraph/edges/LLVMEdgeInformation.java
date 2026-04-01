package aprove.input.Programs.llvm.segraph.edges;

import java.util.*;

import org.json.*;

import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.JSON.*;

/**
 * Specifies the kind of edges which are added to the graph. Stores state change information in form of relations,
 * which can be transformed into conditions for TRSs.
 * NOTE: If the change is not representable as condition in the TRS, "TRUE" is a fine condition.
 * @author Janine Repke, Marc Brockschmidt, cryingshadow
 */
public abstract class LLVMEdgeInformation implements JSONExport, TRSTermExpressible {

    /**
     * The set of relations representing changes that occurred between the source and target state.
     */
    private final Set<LLVMRelation> changesOnEdge;

    /**
     * Initialize a new edge.
     * @param stateChanges A set of changes between the source and target of this edge.
     */
    public LLVMEdgeInformation(Set<? extends LLVMRelation> stateChanges) {
        this.changesOnEdge = new LinkedHashSet<LLVMRelation>(stateChanges);
    }

//    /**
//     * @param startNodeTerm The left-hand side of the rule to generate.
//     * @param endNodeTerm The right-hand side of the rule to generate.
//     * @param conditionTerm The condition of the rule to generate.
//     * @return A triple of the three specified terms where a substitution according to the state change information
//     *         stored in this edge has been applied.
//     */
//    public abstract Triple<TRSFunctionApplication, TRSFunctionApplication, TRSTerm> applySubstitutionsToRuleTerms(
//        TRSFunctionApplication startNodeTerm,
//        TRSFunctionApplication endNodeTerm,
//        TRSTerm conditionTerm
//    );
//
    /**
     * @return The set of relations representing changes that occurred between the source and target state.
     */
    public Set<LLVMRelation> getChangesOnEdge() {
        return this.changesOnEdge;
    }

//    /**
//     * @return the information in this edge label as a set of relations
//     * A model satisfying these relations represents
//     * a pair of concrete states linked by the edge
//     */
//    public IntegerRelationSet getConstraints() {
//        IntegerRelationSet constraints = new IntegerRelationSet();
//        for (LLVMStateChangeInformation stateChange : this.changesOnEdge
//        ) {
//            if (stateChange instanceof LLVMRelation) {
//                constraints.add((LLVMRelation) stateChange);
//            }
//        }
//        return constraints;
//    }
//
    /**
     * @return a String used as color for this edge when rendering a llvm graph to Dot.
     */
    public abstract String getDotColor();

    /**
     * @return a String used as label for this edge when rendering a llvm graph to Dot.
     */
    public abstract String getDotLabel();

    @Override
    public JSONObject toJSON() {
        JSONObject res = new JSONObject();
        res.put("type", this.getClass().getSimpleName());
        res.put("change_info", JSONExportUtil.toJSON(this.changesOnEdge));
        return res;
    }

    @Override
    public TRSTerm toTerm() {
        return LLVMRelationUtils.toTerm(this.getChangesOnEdge());
    }

    /**
     * @param strBuilder a String builder to which a description of the changes on this edge is appended
     */
    protected void getDotLabel(StringBuilder strBuilder) {
        if (!this.changesOnEdge.isEmpty()) {
            strBuilder.append(" (");
            ObjectUtils.binaryStringFold(this.changesOnEdge, ", ", strBuilder);
            strBuilder.append(")");
        }
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("{");
        sb.append("type: ");
        sb.append(this.getClass().getSimpleName());
        sb.append(", ");
        sb.append("changes: ");
        sb.append(this.changesOnEdge);
        sb.append("}");
        return sb.toString();
    }
}
