package aprove.verification.oldframework.Bytecode.Utils.MethodSummary;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;

public enum PredicateType {
    NULL("null"),
    NOT_NULL("not_null"),
    // Integer relations:
    EQ("="),
    GE(">="),
    GT(">"),
    LE("<="),
    LT("<"),
    NE("!="),
    // Predicates
    SHARE("-><-"),
    EQUALS("=?="),
    CYCLIC("cyclic"),
    NON_TREE("non_tree"),
    DEFINITE_REACHABILITY("definite_reachability"),
    REACHABLE_TYPES("reachable_types"),
    INSTANCEOF("instanceof");

    public final String synonym;

    PredicateType(String synonym) {
        this.synonym = synonym;
    }

    public static PredicateType getByString(String predicate) {
        for (PredicateType e : PredicateType.values()) {
            if (e.toString().equalsIgnoreCase(predicate) || e.synonym.equalsIgnoreCase(predicate)) {
                return e;
            }
        }
        return null;
    }

    public IntegerRelationType getIntegerRelationType() {
        for (IntegerRelationType e : IntegerRelationType.values()) {
            if (e.getName().equalsIgnoreCase(synonym)) {
                return e;
            }
        }
        return null;
    }

    public boolean isIntegerRelation() {
        return getIntegerRelationType() != null;
    }

    public boolean needsNoRefinement() {
        return this == SHARE
               || this == EQUALS
               || this == CYCLIC
               || this == NON_TREE
               || this == DEFINITE_REACHABILITY
               || this == REACHABLE_TYPES
               || this == INSTANCEOF;
    }
}
