package aprove.xml;

import java.math.*;

import org.w3c.dom.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;

/**
 * Class for having all strings of the cpf.xsd
 *
 * @author ckuknat
 */
public enum CPFTag {
    PROOF("proof"), //
    UNKNOWN_PROOF("unknownProof"), //
    UNKNOWN_INPUT("unknownInput"), //
    UNKNOWN_INPUT_PROOF("unknownInputProof"), //
    UNKNOWN_ASSUMPTION("unknownAssumption"), //
    UNKNOWN_OBLIGATION("unknownObligation"), //
    DESCRIPTION("description"),
    SUB_PROOF("subProof"),
    TRS_TERMINATION_PROOF("trsTerminationProof"),
    PTRS_TERMINATION_PROOF("ptrsTerminationProof"),
    PTRS_COMPLEXITY_PROOF("ptrsComplexityProof"),
    AC_TERMINATION_PROOF("acTerminationProof"),
    //
    R_IS_EMPTY("rIsEmpty"),
    AC_R_IS_EMPTY("acRIsEmpty"),
    //
    QUASI_REDUCTIVE_PROOF("quasiReductiveProof"),
    UNRAVELING("unraveling"),
    UNRAVEL_INFO("unravelingInformation"),
    UNRAVEL_ENTRY("unravelingEntry"),

    RULE_REMOVAL("ruleRemoval"),
    AC_RULE_REMOVAL("acRuleRemoval"),
    REMOVE_NON_APPLICABLE_RULES("removeNonApplicableRules"),
    EQUALITY_REMOVAL("equalityRemoval"),
    //
    DP_TRANS("dpTrans"), //
    AC_DP_TRANS("acDependencyPairs"), //
    SEMLAB("semlab"), //
    UNLAB("unlab"), //
    STRING_REVERSAL("stringReversal"), //
    RENAMING("renaming"), //
    RENAMING_ENTRY("renamingEntry"), //
    CONSTANT_TO_UNARY("constantToUnary"), //
    FLAT_CONTEXT_CLOSURE("flatContextClosure"), //
    TERMINATION_ASSUMPTION("terminationAssumption"), //
    UNCURRY("uncurry"), //
    BOUNDS("bounds"), //
    SWITCH_INNERMOST("switchInnermost"), //
    SPLIT("split"), //

    MATCH("match"), //
    ROOF("roof"), //
    BOUND("bound"), //
    HEIGHT("height"), //

    TRS_NONTERMINATION_PROOF("trsNonterminationProof"), //
    PTRS_NONTERMINATION_PROOF("ptrsNonterminationProof"), //
    VARIABLE_CONDITION_VIOLATED("variableConditionViolated"), //
    LOOP("loop"), //
    SUBSTITUTIONS("substitutions"), //
    BOX("box"),
    FUN_CONTEXT("funContext"), //
    BEFORE("before"), //
    AFTER("after"), //
    RELATIVE_STEP("relative"), //

    STRING("string"),
    OVERLAP_CLOSURE("overlapClosureSRS"),
    DERIVATION_PATTERN_PROOF("derivationPatternProof"),
    DERIVATION_PATTERNS("derivationPatterns"),
    DERIVATION_PATTERN("derivationPattern"),
    WORD_PATTERN("wordPattern"),
    FACTOR("factor"),
    CONSTANT("constant"),
    OC1("OC1"),
    OC2("OC2"),
    OC2prime("OC2prime"),
    OC3("OC3"),
    OC3prime("OC3prime"),
    LIFT("lift"),
    EQUIVALENT("equivalent"),
    OC_DP1("OCintoDP1"),
    OC_DP2("OCintoDP2"),
    DP_OC_1_1("DP_OC_1_1"),
    DP_OC_1_2("DP_OC_1_2"),
    DP_OC_2("DP_OC_2"),
    DP_OC_3_1("DP_OC_3_1"),
    DP_OC_3_2("DP_OC_3_2"),
    DP_DP_1_1("DP_DP_1_1"),
    DP_DP_1_2("DP_DP_1_2"),
    DP_DP_2_1("DP_DP_2_1"),
    DP_DP_2_2("DP_DP_2_2"),
    SELF_EMBEDDING_OC("selfEmbeddingOC"),
    SELF_EMBEDDING_DP("selfEmbeddingDP"),
    NONTERMINATING_SRS("nonterminatingSRS"),


    NON_LOOP("nonLoop"), //
    PATTERN_RULE("patternRule"), //
    PATTERN_TERM("patternTerm"), //
    EQUIVALENCE("equivalence"), //
    ORIGINAL_RULE("originalRule"), //
    INITIAL_PUMPING("initialPumping"), //
    INITIAL_PUMPING_CONTEXT("initialPumpingContext"), //
    NARROWING("narrowing"), //
    INSTANTIATION("instantiation"), //
    REWRITING("rewriting"), //
    LEFT("left"), //
    RIGHT("right"), //
    PATTERN_EQUIVALENCE("patternEquivalence"), //
    INSTANTIATION_PUMPING("instantiationPumping"), //
    POWER("power"),
    DOMAIN_RENAIMING("domainRenaming"), //
    IRRELEVANT("irrelevant"), //
    SIMPLIFICATION("simplification"), //
    CLOSING("closing"), //
    PUMPING("pumping"), //
    BASE("base"), //
    IS_PAIR("isPair"), //

    NONTERMINATION_ASSUMPTION("nonterminationAssumption"), //
    INNERMOST_LHSS_INCREASE("innermostLhssIncrease"), //

    DP_PROOF("dpProof"), //
    DT_PROOF("dtProof"), //
    AC_DP_PROOF("acDPTerminationProof"), //
    DEP_GRAPH_PROC("depGraphProc"), //
    AC_DEP_GRAPH_PROC("acDepGraphProc"), //
    P_IS_EMPTY("pIsEmpty"), //
    D_ABS_IS_EMPTY("DAbsIsEmpty"), //
    AC_P_IS_EMPTY("acTrivialProc"), //
    RED_PAIR_PROC("redPairProc"), //
    AC_RED_PAIR_PROC("acRedPairProc"), //
    RED_PAIR_UR_PROC("redPairUrProc"), //
    MONO_RED_PAIR_PROC("monoRedPairProc"), //
    AC_MONO_RED_PAIR_PROC("acMonoRedPairProc"), //
    MONO_RED_PAIR_UR_PROC("monoRedPairUrProc"), //
    SUBTERM_PROC("subtermProc"), //
    SEMLAB_PROC("semlabProc"), //
    UNLAB_PROC("unlabProc"), //
    SIZE_CHANGE_PROC("sizeChangeProc"), //
    FLAT_CONTEXT_CLOSURE_PROC("flatContextClosureProc"), //
    ARGUMENT_FILTER_PROC("argumentFilterProc"), //
    UNCURRY_PROC("uncurryProc"), //
    FINITENESS_ASSUMPTION("finitenessAssumption"), //
    USABLE_RULES_PROC("usableRulesProc"), //
    INNERMOST_LHSS_REMOVAL_PROC("innermostLhssRemovalProc"), //
    SWITCH_INNERMOST_PROC("switchInnermostProc"), //
    REWRITING_PROC("rewritingProc"), //
    FORWARD_INSTANTIATION_PROC("forwardInstantiationProc"), //
    NARROWING_PROC("narrowingProc"), //
    SPLIT_PROC("splitProc"), //
    GENERAL_RED_PAIR_PROC("generalRedPairProc"), //
    DP_TO_TRS_PROC("switchToTRS"),

    DP_NONTERMINATION_PROOF("dpNonterminationProof"), //
    DP_RULE_REMOVAL("dpRuleRemoval"), //
    INFINITENESS_ASSUMPTION("infinitenessAssumption"), //
    INNERMOST_LHSS_INCREASE_PROC("innermostLhssIncreaseProc"), //
    SWITCH_FULL_STRATEGY_PROC("switchFullStrategyProc"), //
    SWITCH_FULL_STRATEGY("switchFullStrategy"), //
    INSTANTIATION_PROC("instantiationProc"), //

    NAME("name"), //
    ARITY("arity"), //
    SHARP("sharp"), //
    LABELED_SYMBOL("labeledSymbol"), //
    NUMBER_LABEL("numberLabel"), //
    SYMBOL_LABEL("symbolLabel"), //
    NUMBER("number"), //

    ARGUMENT_FILTER("argumentFilter"), //
    ARGUMENT_FILTER_ENTRY("argumentFilterEntry"), //
    COLLAPSING("collapsing"), //
    NON_COLLAPSING("nonCollapsing"), //

    POLYNOMIAL("polynomial"), //
    MONOMIAL("monomial"), //
    ARITH_FUNCTION("arithFunction"), //
    NATURAL("natural"), //
    VARIABLE("variable"), //
    SUM("sum"), //
    PRODUCT("product"), //
    MIN("min"), //
    MAX("max"), //

    CERTIFICATION_PROBLEM("certificationProblem"), //
    INPUT("input"), //
    CPF_VERSION("cpfVersion"), //
    ORIGIN("origin"), //
    PROOF_ORIGIN("proofOrigin"), //
    TOOL("tool"), //
    VERSION("version"), //
    TOOL_USER("toolUser"), //
    FIRST_NAME("firstName"), //
    LAST_NAME("lastName"), //
    INPUT_ORIGIN("inputOrigin"), //

    COEFFICIENT("coefficient"), //
    INTEGER("integer"), //
    RATIONAL("rational"), //
    MINUS_INFINITY("minusInfinity"), //
    PLUS_INFINITY("plusInfinity"), //

    COMPLETION_AND_NORMALIZATION("completionAndNormalization"), //
    COMPLETION_PROOF("completionProof"), //
    COMPLEXITY_PROOF("complexityProof"), //
    COMPLEXITY_ASSUMPTION("complexityAssumption"), //
    DT_TRANSFORMATION("dtTransformation"), //
    WEAK_DTS("weakDTs"),
    STRICT_DTS("strictDTs"),
    RULE_WITH_DT("ruleWithDT"),
    RULE_SHIFTING("ruleShifting"), //
    NON_USABLE_RULES("nonUsableRules"),
    CONVERSION("conversion"), //
    START_TERM("startTerm"), //
    EQUATIONAL_STEP("equationalStep"), //

    CR_PROOF("crProof"), //
    WCR_AND_S_N("wcrAndSN"), //
    ORTHOGONAL("orthogonal"), //

    DEGREE("degree"), //
    DIMENSION("dimension"), //

    DOMAIN("domain"), //
    TYPE("type"), //
    NATURALS("naturals"), //
    INTEGERS("integers"), //
    RATIONALS("rationals"), //
    ARCTIC("arctic"), //
    TROPICAL("tropical"), //
    MATRICES("matrices"), //
    DELTA("delta"),

    DP_INPUT("dpInput"), //
    MINIMAL("minimal"), //

    DPS("dps"), //
    DP_EQUATIONS("dpEquations"), //
    DP_EXTENSIONS("extensions"), //
    EQUATIONAL_DISPROOF("equationalDisproof"), //
    EQUATIONAL_PROOF("equationalProof"), //
    EQUATIONAL_PROOF_TREE("equationalProofTree"), //

    EQUATIONS("equations"), //
    FUNAPP("funapp"), //

    MATRIX_INTERPRETATION("matrixInterpretation"), //
    MATRIX("matrix"), //
    MODEL("model"), //
    FINITE_MODEL("finiteModel"), //
    ROOT_LABELING("rootLabeling"), //
    CARRIER_SIZE("carrierSize"), //
    TUPLE_ORDER("tupleOrder"), //
    POINT_WISE("pointWise"), //

    ORDERING_CONSTRAINT_PROOF("orderingConstraintProof"), //

    POSITION_IN_TERM("positionInTerm"), //
    POSITION("position"), //

    RED_PAIR("redPair"), //
    REDUCTION_PAIR("reductionPair"), //
    INTERPRETATION("interpretation"), //
    INTERPRET("interpret"), //
    PATH_ORDER("pathOrder"), //
    STATUS_PRECEDENCE("statusPrecedence"), //
    STATUS_PRECEDENCE_ENTRY("statusPrecedenceEntry"), //
    MUL("mul"), //
    LEX("lex"), //
    WEIGHT_ZERO("w0"), //
    WEIGHT("weight"), //
    PRECEDENCE("precedence"), //
    PRECEDENCE_WEIGHT("precedenceWeight"), //
    PRECEDENCE_WEIGHT_ENTRY("precedenceWeightEntry"), //
    KNUTH_BENDIX_ORDER("knuthBendixOrder"), //
    SCNP("scnp"), //

    RELATIVE_NONTERMINATION_PROOF("relativeNonterminationProof"), //
    RELATIVE_TERMINATION_PROOF("relativeTerminationProof"), //
    S_IS_EMPTY("sIsEmpty"), //
    RELATIVE_TERMINATION_ASSUMPTION("relativeTerminationAssumption"),

    REWRITE_SEQUENCE("rewriteSequence"), //
    REWRITE_STEP("rewriteStep"), //
    RELATIVE("relative"), //

    RULES("rules"), //
    CONDITIONAL_RULE("conditionalRule"),
    RULE("rule"), //
    LHS("lhs"), //
    RHS("rhs"), //

    SIGNATURE("signature"), //
    SYMBOL("symbol"), //
    STATE("state"), //
    STRATEGY("strategy"), //
    OUTERMOST("outermost"), //
    CONTEXT_SENSITIVE("contextSensitive"), //
    REPLACEMENT_MAP_ENTRY("replacementMapEntry"),
    INNERMOST("innermost"), //
    PARALLEL_INNERMOST("parallelInnermost"), // not yet part of CPF, may need revision
    INNERMOST_LHSS("innermostLhss"), //

    STRICT_DIMENSION("strictDimension"), //
    SUBSTITUTION("substitution"), //
    SUBST_ENTRY("substEntry"), //

    SUBSUMPTION_PROOF("subsumptionProof"), //
    RULE_SUBSUMPTION_PROOF("ruleSubsumptionProof"), //
    EQUATION_STEP("equationStep"), //

    RUNTIME_COMPLEXITY("runtimeComplexity"),
    COMPLEXITY_INPUT("complexityInput"),

    TREE_AUTOMATON("treeAutomaton"), //
    FINAL_STATES("finalStates"), //
    TRANSITIONS("transitions"), //
    TRANSITION("transition"), //

    TRS_INPUT("trsInput"), //
    TRS("trs"), //
    CTRS_INPUT("ctrsInput"), //
    RELATIVE_RULES("relativeRules"), //
    AC_REWRITE_SYSTEM("acRewriteSystem"),
    A_SYMBOLS("Asymbols"),
    C_SYMBOLS("Csymbols"),

    APPLICATIVE_TOP("applicativeTop"),
    UNCURRY_INFORMATION("uncurryInformation"), //
    UNCURRIED_SYMBOLS("uncurriedSymbols"), //
    UNCURRY_RULES("uncurryRules"), //
    ETA_RULES("etaRules"), //
    UNCURRIED_SYMBOL_ENTRY("uncurriedSymbolEntry"), //

    URL("url"), //
    USABLE_RULES("usableRules"), //
    VAR("var"), //
    ARG("arg"), //
    VECTOR("vector"), //
    WCR_PROOF("wcrProof"), //
    JOINABLE_CRITICAL_PAIRS("joinableCriticalPairs"), //
    JOINABLE_CRITICAL_PAIRS_AUTO("joinableCriticalPairsAuto"), //
    JOINABLE_CRITICAL_PAIRS_B_F_S("joinableCriticalPairsBFS"), //

    FRESH_SYMBOL("freshSymbol"), //
    FLAT_CONTEXTS("flatContexts"), //
    COMPOMENT("component"), //
    REAL_SCC("realScc"), //
    SUBTERM_CRITERION("subtermCriterion"), //
    SIZE_CHANGE_GRAPH("sizeChangeGraph"), //
    EDGE("edge"), //
    STRICT("strict"), //
    NON_STRICT("nonStrict"), //
    MARKED_SYMBOLS("markedSymbols"), //
    NUMERATOR("numerator"), //
    DENOMINATOR("denominator"), //

    INSTANTIATIONS("instantiations"), //
    NARROWINGS("narrowings"), //

    COND_RED_PAIR_PROOF("condRedPairProof"), //
    CONDITION("condition"), //
    CONSTRAINT("constraint"), //
    CONDITIONAL_CONSTRAINT("conditionalConstraint"), //
    CONDITIONAL_CONSTRAINT_PROOF("conditionalConstraintProof"), //
    CONDITIONS("conditions"), //
    DP_SEQUENCE("dpSequence"), //
    FINAL("final"), //
    DIFFERENT_CONSTRUCTOR("differentConstructor"),
    DELETE_CONDITION("deleteCondition"),
    SAME_CONSTRUCTOR("sameConstructor"),
    VARIABLE_EQUATION("variableEquation"),
    SIMPLIFY_CONDITION("simplifyCondition"),
    INDUCTION("induction"),
    CONJUNCTS("conjuncts"),
    RULE_CONSTRAINT_PROOFS("ruleConstraintProofs"),
    RULE_CONSTRAINT_PROOF("ruleConstraintProof"),
    SUBTERM_VAR_ENTRIES("subtermVarEntries"),
    SUBTERM_VAR_ENTRY("subtermVarEntry"),
    FUNARG_INTO_VAR("funargIntoVar"),

    COMPLEX_CONSTANT_REMOVAL_PROC("complexConstantRemovalProc"),
    RULE_MAP("ruleMap"),
    RULE_MAP_ENTRY("ruleMapEntry"),

    LTS_INPUT("lts"),
    LTS_INITIAL("initial"),
    LTS_LOCATION("location"),
    LTS_LOCATION_ID("locationId"),
    LTS_LOCATION_DUP("locationDuplicate"),
    LTS_SOURCE("source"),
    LTS_TARGET("target"),
    LTS_TRANSITION_ID("transitionId"),
    LTS_TRANSITION_DUP("transitionDuplicate"),
    LTS_TRANSITION("transition"),
    LTS_FORMULA("formula"),
    LTS_CONJUNCTION("conjunction"),
    LTS_VARIABLE_ID("variableId"),
    LTS_POST_VARIABLE("post"),
    LTS_EQ("eq"),
    LTS_LEQ("leq"),
    LTS_LESS("less"),
    LTS_CONSTANT("constant"),
    LTS_SUM("sum"),
    LTS_PRODUCT("product"),
    LTS_TERMINATION_PROOF("ltsTerminationProof"),
    LTS_SWITCH_COOPERATION("switchToCooperationTermination"),
    LTS_SKIP_ID("skipId"),
    LTS_SKIP_FORMULA("skipFormula"),
    LTS_CUT_POINTS("cutPoints"),
    LTS_CUT_POINT("cutPoint"),
    LTS_SCC_DECOMP("sccDecomposition"),
    LTS_SCC_PROOF("sccWithProof"),
    LTS_SCC("scc"),
    LTS_TRANSITION_REMOVAL("transitionRemoval"),
    LTS_TRIVIAL("trivial"),
    LTS_BOUND("bound"),
    LTS_RANKING_FUNCTIONS("rankingFunctions"),
    LTS_RANKING_FUNCTION("rankingFunction"),
    LTS_EXPRESSION("expression"),
    LTS_REMOVE("remove"),


    LLVM_SEG_PROOF("llvmSymbolicExecGraphProof"),
    LLVM_PROG("llvmProg"),

    ;

    private final String tag;

    private CPFTag(final String tag) {
        this.tag = tag;
    }

    public final Element create(final Document doc) {
        return doc.createElement(this.tag);
    }

    public final Element createElement(final Document doc) {
        return doc.createElement(this.tag);
    }

    public final Element create(final Document doc, final Text text) {
        final Element main = doc.createElement(this.tag);
        main.appendChild(text);
        return main;
    }

    public final Element create(final Document doc, final String s) {
        return this.create(doc, doc.createTextNode(s));
    }

    public final Element create(final Document doc, final BigInteger i) {
        return this.create(doc, i.toString());
    }

    public final Element create(final Document doc, final int i) {
        return this.create(doc, Integer.toString(i));
    }

    public static Element notYetImplemented(final Document doc, final Object o) {
        return CPFTag.UNKNOWN_PROOF.create(doc, doc.createTextNode(o.getClass().getCanonicalName()));
    }

    public final Element create(final Document doc, final Element... elements) {
        final Element main = doc.createElement(this.tag);
        for (final Element e : elements) {
            main.appendChild(e);
        }
        return main;
    }

    public static final Element rules(final Document doc, final XMLMetaData xmlMetaData, final Iterable<? extends GeneralizedRule> rules) {
        final Element e = CPFTag.RULES.create(doc);
        for (final GeneralizedRule rule : rules) {
            e.appendChild(rule.toCPF(doc, xmlMetaData));
        }
        return e;
    }

    public static final Element probabilisticRules(final Document doc, final XMLMetaData xmlMetaData, final Iterable<? extends GeneralizedProbabilisticRule> rules) {
        final Element e = CPFTag.RULES.create(doc);
        for (final GeneralizedProbabilisticRule rule : rules) {
            e.appendChild(rule.toCPF(doc, xmlMetaData));
        }
        return e;
    }

    public static final Element equationRules(final Document doc, final XMLMetaData xmlMetaData, final Iterable<? extends Equation> rules) {
        final Element e = CPFTag.RULES.create(doc);
        for (final Equation rule : rules) {
            e.appendChild(rule.toCPFasRule(doc, xmlMetaData));
        }
        return e;
    }

    public static final Element trs(final Document doc, final XMLMetaData xmlMetaData, final Iterable<? extends GeneralizedRule> rules) {
        return CPFTag.TRS.create(doc, CPFTag.rules(doc, xmlMetaData, rules));
    }

    public static final Element dps(final Document doc, final XMLMetaData xmlMetaData, final Iterable<? extends GeneralizedRule> rules) {
        return CPFTag.DPS.create(doc, CPFTag.rules(doc, xmlMetaData, rules));
    }

    public static final Element adp(final Document doc, final XMLMetaData xmlMetaData, final Iterable<? extends GeneralizedRule> rules) {
        return CPFTag.TRS.create(doc, CPFTag.rules(doc, xmlMetaData, rules));
    }

    public static final Element ptrs(final Document doc, final XMLMetaData xmlMetaData, final Iterable<? extends GeneralizedProbabilisticRule> rules) {
        return CPFTag.TRS.create(doc, CPFTag.probabilisticRules(doc, xmlMetaData, rules));
    }

    public static final Element createError(final Document doc) {
        return doc.createElement("ERROR");
    }

    public static final Element createIdentifier(final Document doc, final String id) {
        final Element e = doc.createElement("identifier");
        e.setAttribute("name", id);
        return e;
    }

}

