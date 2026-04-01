package aprove.xml;

import java.math.*;

import org.w3c.dom.*;

public enum XMLTag { FUNCTION_SYMBOL("symbol"),
                     FUNCTION_SYMBOLS("function-symbols"),
                     LABELED_SYMBOL("labeledSymbol"),
                     LABEL("label"),
                     POSITION("position"),
                     SIGNATURE("signature"),
                     UNKNOWN_OBLIGATION("text-obligation"),
                     UNKNOWN_PROOF("text-proof"),
                     UNKNOWN_ORDER("text-order"),
                     QTRS_OBL("qtrs-termination-obligation"),
                     GTRS_OBL("gtrs-termination-obligation"),
                     RELTRS_OBL("reltrs-termination-obligation"),
                     QTRS("qtrs"),
                     GTRS("gtrs"),
                     ETRS("etrs"),
                     RELTRS("reltrs"),
                     CSR("csr"),
                     TRS("trs"),
                     LHS("lhs"),
                     RHS("rhs"),
                     QDP("qdp"),

                     BOUND_PROOF("qtrs-bound-proof"),
                     BOUND_TYPE("bound-type"),
                     FINAL_STATES("final-states"),
                     STATE("state"),
                     TREE_AUTOMATON("tree-automaton"),
                     TRANSITION("transition"),
                     TRANSITION_RHS("transition-rhs"),
                     TRANSITION_LHS("transition-lhs"),
                     HEIGHT("height"),

                     QDP_UNCURRYING_PROOF("qdp-uncurrying-proof"),
                     QDP_APPLICATIVE_TOP("applicative-top"),
                     UNCURRY_INFORMATION("uncurry-information"),
                     UNCURRY_INFORMATION_ENTRY("uncurry-information-entry"),
                     SYMBOL_ENTRIES("symbol-entries"),

                     ETRS_TO_RELTRS_PROOF("etrs-to-reltrs-proof"),

                     DPS("dps"),
                     DP_EDGE("dp-edge"),
                     MINIMALITY("minimality-flag"),
                     MINIMALITY_VALUE("value"),
                     INNERMOST("innermost"),
                     QDP_OBL("qdp-termination-obligation"),
                     TERM("term"),
                     FUNCTION_APPLICATION("fun-app"),
                     RULE("rule"),
                     EQUATIONS("equations"),
                     EQUATION("equation"),
                     VARIABLE("variable"),
                     QTERMSET("qtermset"),
                     SUBSTITUTION("substitution"),
                     SUBSTITUTE("substitute"),

                     PROBABILISTICRULE("probabilistic-rule"),
                     PROBABILISTICDEPTUPLE("probabilistic-dependency-tuple"),
                     PAIR("pair"),
                     DISTRIBUTION("distribution"),
                     FRACTION("fraction"),
                     SET("set"),

                     GTRS_CRIT_RULE_PROOF("gtrs-crit-rule-proof"),
                     QTRS_NONTERMINATION_PROOF("qtrs-nontermination-proof"),
                     QDP_NONTERMINATION_PROOF("qdp-nontermination-proof"),
                     QDP_REWRITE_SEQUENCE("qdp-rewrite-sequence"),
                     RELTRS_NONTERMINATION_PROOF("reltrs-nontermination-proof"),
                     // the SRS non-termination proofs are necessary for CoLoR,
                     // because it expects those in a different format
                     QSRS_NONTERMINATION_PROOF("qsrs-nontermination-proof"),
                     RELSRS_NONTERMINATION_PROOF("relsrs-nontermination-proof"),
                     LOOP("loop"),
                     STEP("step"),
                     // a relative step consists of a sequence of S-steps,
                     // followed by an ordinary (R-)step.
                     RELATIVE_STEP("relative-step"),
                     S_STEPS("s-steps"),

                     CONTEXT("context"),
                     BOX("box"),

                     QDP_NONLOOP_PROOF("qdp-nonloop-proof"),
                     PROOFED_RULE("proofed-rule"),
                     PATTERN_RULE("pattern-rule"),
                     PATTERN_TERM("pattern-term"),
                     ORIGINAL_RULE("original-rule"),
                     INITIAL_PUMPING("initial-pumping"),
                     INITIAL_PUMPING_CONTEXT("initial-pumping-context"),
                     EQUIVALENCE("equivalence"),
                     PATTERN_EQUIVALENCE("pattern-equivalence"),
                     NARROWING("narrowing"),
                     INSTANTIATION("instantiation"),
                     BASE("base"),
                     PUMPING("pumping"),
                     CLOSING("closing"),
                     REWRITING("rewriting"),
                     DOMAIN_RENAIMING("domain-renaming"),
                     IRRELEVANT("irrelevant"),
                     SIMPLIFICATION("simplification"),
                     LEFT("left"),
                     RIGHT("right"),

                     QTRS_REVERSE_PROOF("qtrs-reverse-proof"),
                     RELTRS_REVERSE_PROOF("reltrs-reverse-proof"),
                     RELTRS_CLEAN_PROOF("reltrs-clean-proof"),
                     RELTRS_EMPTY_S_PROOF("reltrs-empty-s-proof"),
                     SRS_AS_TRS_PROOF("srs-as-trs-proof"),

                     QTRS_LCO_PROOF("qtrs-locally-confluent-overlay-proof"),

                     QTRS_RULE_REMOVAL_PROOF("qtrs-rule-removal-proof"),
                     RELTRS_RULE_REMOVAL_PROOF("reltrs-rule-removal-proof"),
                     CSR_RULE_REMOVAL_PROOF("csr-rule-removal-proof"),

                     QTRS_Q_RULE_REMOVAL_PROOF("qtrs-q-rule-removal-proof"),

                     QTRS_DEPENDENCY_PAIRS_PROOF("qtrs-dependency-pairs-proof"),
                     DEFINED_TO_TUPLE("defined-to-tuple-entry"),
                     RULE_TO_DPS("rule-to-dps-entry"),
                     POSITION_TO_DP("position-to-dp"),

                     QDP_SIZE_CHANGE_PROOF("qdp-size-change-proof"),
                     SUBTERM_CRITERION("subterm-criterion"),
                     QDP_SIZE_CHANGE_GRAPH("qdp-size-change-graph"),
                     EDGE("edge"),

                     QDP_SUBTERM_PROOF("qdp-subterm-proof"),
                     QDP_REDUCTION_PAIR_PROOF("qdp-reduction-pair-proof"),
                     QDP_BOUNDED_INCREASE_PROOF("qdp-bounded-increase-proof"),
                     QDP_USABLE_RULES_PROOF("qdp-usable-rules-proof"),
                     QDP_COMPLEX_CONSTANT_REMOVAL_PROOF("qdp-complex-constant-removal-proof"),
                     QDP_MNOC_PROOF("qdp-mnoc-proof"),
                     QDP_REVERSE_MNOC_PROOF("qdp-reverse-mnoc-proof"),
                     QDP_MONO_REDUCTION_PAIR_UR_PROOF("qdp-mono-reduction-pair-ur-proof"),
                     QDP_MONO_REDUCTION_PAIR_PROOF("qdp-mono-reduction-pair-proof"),
                     QDP_QREDUCTION("qdp-q-reduction-proof"),

                     QDP_DEPENDENCY_GRAPH_PROOF("qdp-dependency-graph-proof"),
                     QDP_SCC("graph-scc"),
                     QDP_NON_SCC("non-scc"),

                     QTRS_ROOT_LABELING("qtrs-root-labeling-proof"),
                     QDP_ROOT_LABELING_FC1("qdp-root-labeling-fc1-proof"),
                     QTRS_FLAT_CC("qtrs-flat-cc-proof"),
                     QDP_FLAT_CC("qdp-flat-cc-proof"),
                     FLAT_CONTEXT("flat-context"),

                     QDP_SPLIT("qdp-split-proof"),
                     QTRS_SPLIT("qtrs-split-proof"),
                     QTRS_SEMANTIC_LABELING("qtrs-semantic-labeling-proof"),
                     QDP_SEMANTIC_LABELING("qdp-semantic-labeling-proof"),
                     QDP_SEMANTIC_LABELING2("qdp-semantic-labeling-proof2"),
                     CARRIER_SIZE("carrier-size"),
                     MODEL("model"),
                     INTERPRET("interpret"),


                     QDP_EDGE_DELETION_PROOF("qdp-edge-deletion-proof"),
                     QDP_EDGE_DELETION("edge-deletion"),
                     QDP_EDGE_DELETION_REASON("edge-del-reason"),
                     DIFFERENT_ROOTS("different-roots"),
                     EDG_NON_UNIF("capt-not-unifies-u"),
                     EDG_NON_NORMAL("capt-u-mgu-not-normal"),
                     EDGSTAR_NON_UNIF("capu-not-unifies-t"),
                     EDGSTAR_NON_NORMAL("capu-t-mgu-not-normal"),

                     P_IS_EMPTY_PROOF("p-is-empty-proof"),
                     R_IS_EMPTY_PROOF("r-is-empty-proof"),
                     REL_R_IS_EMPTY_PROOF("rel-r-is-empty-proof"),

                     ORDER("order"),

                     POLO("polynomial-order"),
                     SCNP("scnp-order"),
                     SCNP_REDUCTION_PAIR_PROOF("scnp-reduction-pair-proof"),
                     SCNP_STATUS("scnp-status"),
                     LEVEL_MAPPING("scnp-level-mapping"),
                     LEVEL_MAPPING_ENTRY("level-mapping-entry"),
                     POSITION_LEVEL_ENTRY("position-level-entry"),
                     LEVEL("level"),
                     NEG_POLO("neg-polynomial-order"),
                     POLO_INTERPRETATION("polo-interpretation"),
                     POLYNOMIAL("polynomial"),
                     DEGREE("degree"),
                     MONOMIAL("monomial"),
                     INDEFINIT("polo-factor"),
                     RATIONAL("rational"),
                     NUMERATOR("numerator"),
                     DENOMINATOR("denominator"),
                     DELTA("delta"),


                     MAX("max"),
                     MIN("min"),

                     MATRO("matrix-order"),
                     MATRIX_INTERPRETATION("matrix-interpretation"),
                     MPOLYNOMIAL("mpolynomial"),
                     MMONOMIAL("mmonomial"),
                     MATRIX("matrix"),
                     MVECT("mvect"),

                     EMB_ORDER("emb-order"),
                     PATH_ORDER("path-order"),
                     AFS("afs"),
                     FILTER("filter"),
                     COLLAPSE("collapse"),
                     FILTERING("filtering"),
                     PRECEDENCE("precedence"),
                     PREC("prec"),
                     STATUS_MAP("statusMap"),
                     STATUS("status"),
                     MULTISET("multiset"),
                     LEXICOGRAPHIC("lex"),
                     ARGUMENT("arg"),

                     CONJUNCTION("conjunction"),
                     DISJUNCTION("disjunction"),
                     PROVED("proved"),
                     DISPROVED("disproved"),

                     OBL("proof-obligation"),
                     PROPOSITION("proposition"),
                     BASIC_OBL("basic-obligation"),

                     PROOF("proof"),

                     IMPLICATION("implication"),

                     IDP_PROCESSOR_TYPE("idp-processorType"),
                     IDP_PROCESSOR_TYPE_MAIN("idp-processorType-main"),
                     IDP_PROCESSOR_TYPE_SUB("idp-processorType-sub"),
                     IDP_PROCESSOR_TYPE_SUBSUB("idp-processorType-subSub"),

                     DIO_CONSTRAINTS("dio-constraints"),
                     DIO_CONSTRAINT("dio-constraint"),
                     DIO_NO_SOLUTION("dio-no-solution"),
                     DIO_SOLUTION("dio-solution"),
                     DIO_ASSIGNMENT("dio-assignment"),
                     DIO_SUM("dio-sum"),
                     DIO_PRODUCT("dio-product"),

                     FORWARD_INSTANTIATION_PROOF("forward-instantiation-proof"),
                     INSTANTIATION_PROOF("instantiation-proof"),
                     NARROWING_PROOF("narrowing-proof"),
                     REWRITING_PROOF("rewriting-proof"),

                     BOUNDED_INCREASE_PROOF("bounded-increase-proof"),
                     ;

    private final String tag;

    private XMLTag(final String tag) {
        this.tag = tag;
    }

    public final Element createElement(final Document doc) {
        return doc.createElement(this.tag);
    }

    public static final Element createError(final Document doc) {
        return doc.createElement("ERROR");
    }

    public static final Element createBoolean(final Document doc, final boolean b) {
        final Element e = doc.createElement("boolean");
        e.setAttribute("value", b ? "true" : "false");
        return e;
    }

    public static final Element createInteger(final Document doc, final String i) {
        final Element e = doc.createElement("integer");
        e.setAttribute("value", i);
        return e;
    }

    public static final Element createInteger(final Document doc, final int i) {
        return XMLTag.createInteger(doc, ""+i);
    }

    public static final Element createArcticInt(final Document doc, final boolean infinity, final BigInteger value) {
        final Element e = doc.createElement("arctic-int");
        e.setAttribute("infinite", String.valueOf(infinity));
        if (!infinity) {
            e.setAttribute("value", value.toString());
        }
        return e;
    }

    public static final Element createIdentifier(final Document doc, final String id) {
        final Element e = doc.createElement("identifier");
        e.setAttribute("name", id);
        return e;
    }

}

