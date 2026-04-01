package aprove.verification.dpframework.DPConstraints;

public enum InfRuleID {
    I,
    II,
    I_II("(I) and (II)"),
    III,
    IV,
    V("(V) (with possible (I) afterwards)"),
    VI,
    VII,
    DEPRECATED,
    IDP_CONSTANT_FOLD,
    POLY_CONSTRAINTS,
    IDP_SMT_SPLIT,
    POLY_REMOVE_MIN_MAX,
    POLY_EXTRACT_COMPARISONS,
    DELETE_TRIVIAL_REDUCESTO,
    REPLACE_CONTEXT_PREDEF_FUNCTIONS,
    IDP_BOOLEAN,
    FIXED_INT_CONST,
    REWRITING,
    IDP_REPLACE_BYVAR,
    IDP_UNRESTRICTED_VARS,
    IDP_POLY_SIMPLIFY,
    IDP_POLY_GCD;

    private final String name;

    InfRuleID() {
        this.name = "(" + this.name() + ")";
    }

    InfRuleID(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return this.name;
    }
}
