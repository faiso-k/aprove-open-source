package aprove.input.Programs.prolog;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;

/**
 * @author cryingshadow
 * Gathers some collections and methods concerning built-in predicates and constructor symbols in ISO Prolog.
 */
public abstract class PrologBuiltins {

    /**
     * A collection of the six arithmetic comparison predicates in ISO Prolog.
     */
    public static final Collection<FunctionSymbol> ARITHMETIC_COMPARISON_PREDICATES = PrologBuiltins
        .getArithmeticComparisonPredicates();

    /**
     * A collection of operators which can be used in arithmetic expressions (e.g., +,-,*,...).
     */
    public static final Collection<FunctionSymbol> ARITHMETIC_OPERATORS = PrologBuiltins.getArithmeticOperators();

    /**
     * A collection containing all built-in predicate names according to the ISO standard.
     */
    public static final Collection<String> BUILTIN_PREDICATE_NAMES = PrologBuiltins.getNamesOfBuiltinPredicates();

    /**
     * A collection containing all built-in predicates according to the ISO standard.
     */
    public static final Collection<FunctionSymbol> BUILTIN_PREDICATES = PrologBuiltins.getBuiltinPredicates();

    /**
     * A collection containing the names of all goal junctors (',', ';', and '->').
     */
    public static final Collection<String> GOAL_JUNCTOR_NAMES = PrologBuiltins.getGoalJunctorNames();

    /**
     * A collection containing the names of all goal junctors (',', ';', and '->').
     */
    public static final Collection<FunctionSymbol> GOAL_JUNCTORS = PrologBuiltins.getGoalJunctors();

    /**
     * A collection containing all built-in predicates using meta-calls.
     */
    public static final Collection<FunctionSymbol> META_BUILTIN_PREDICATES = PrologBuiltins.getMetaBuiltinPredicates();

    /**
     * A mapping from recursive built-in predicates to the number of resulting state elements without question marks.
     */
    public static final Map<FunctionSymbol, Integer> RECURSIVE_BUILTIN_PREDICATES = PrologBuiltins
        .getRecursiveBuiltinPredicates();

    /**
     * @param name A name of a function symbol.
     * @return A representation of the specified name which is suitable for LaTeX documents.
     */
    public static String toLaTeX(final String name) {
        if (name.equals(PrologBuiltin.EMPTY_LIST_CONSTRUCTOR_NAME)) {
            return "emptyList";
        } else if (name.equals(PrologBuiltin.LIST_CONSTRUCTOR_NAME)) {
            return "listCons";
        } else if (name.equals(PrologBuiltin.CUT_NAME)) {
            return "cut";
        } else if (name.equals(PrologBuiltin.UNIFY_NAME)) {
            return "unify";
        } else {
            return name;
        }
    }

    /**
     * @return The first 50% of all builtin predicate names (because checkstyle moans if we add all at once...).
     */
    private static Collection<String> get1stHalfOfBuiltinPredicateNames() {
        final Collection<String> res = new ArrayList<String>();
        res.add(PrologBuiltin.ABOLISH_NAME);
        res.add(PrologBuiltin.CONJUNCTION_NAME);
        res.add(PrologBuiltin.ARG_NAME);
        res.add(PrologBuiltin.ASSERTA_NAME);
        res.add(PrologBuiltin.ASSERTZ_NAME);
        res.add(PrologBuiltin.AT_END_OF_STREAM_NAME);
        res.add(PrologBuiltin.ATOM_CHARS_NAME);
        res.add(PrologBuiltin.ATOM_CODES_NAME);
        res.add(PrologBuiltin.ATOM_CONCAT_NAME);
        res.add(PrologBuiltin.ATOM_LENGTH_NAME);
        res.add(PrologBuiltin.ATOM_NAME);
        res.add(PrologBuiltin.ATOMIC_NAME);
        res.add(PrologBuiltin.BAGOF_NAME);
        res.add(PrologBuiltin.CALL_NAME);
        res.add(PrologBuiltin.CATCH_NAME);
        res.add(PrologBuiltin.CHAR_CODE_NAME);
        res.add(PrologBuiltin.CHAR_CONVERSION_NAME);
        res.add(PrologBuiltin.CLAUSE_NAME);
        res.add(PrologBuiltin.CLOSE_NAME);
        res.add(PrologBuiltin.COMPOUND_NAME);
        res.add(PrologBuiltin.COPY_TERM_NAME);
        res.add(PrologBuiltin.CURRENT_CHAR_CONVERSION_NAME);
        res.add(PrologBuiltin.CURRENT_INPUT_NAME);
        res.add(PrologBuiltin.CURRENT_OP_NAME);
        res.add(PrologBuiltin.CURRENT_OUTPUT_NAME);
        res.add(PrologBuiltin.CURRENT_PROLOG_FLAG_NAME);
        res.add(PrologBuiltin.CUT_NAME);
        res.add(PrologBuiltin.EQUALS_NAME);
        res.add(PrologBuiltin.FAIL_NAME);
        res.add(PrologBuiltin.FINDALL_NAME);
        res.add(PrologBuiltin.FLOAT_NAME);
        res.add(PrologBuiltin.FLUSH_OUTPUT_NAME);
        res.add(PrologBuiltin.FUNCTOR_NAME);
        res.add(PrologBuiltin.GEQ_NAME);
        res.add(PrologBuiltin.GET_BYTE_NAME);
        res.add(PrologBuiltin.GET_CHAR_NAME);
        res.add(PrologBuiltin.GET_CODE_NAME);
        res.add(PrologBuiltin.GREATER_NAME);
        res.add(PrologBuiltin.HALT_NAME);
        res.add(PrologBuiltin.IF_NAME);
        res.add(PrologBuiltin.INTEGER_NAME);
        res.add(PrologBuiltin.IS_NAME);
        res.add(PrologBuiltin.ISEQUAL_NAME);
        res.add(PrologBuiltin.ISUNEQUAL_NAME);
        return res;
    }

    /**
     * @return The first 33% of all builtin predicates (because checkstyle moans if we add all at once...).
     */
    private static Collection<FunctionSymbol> get1stThirdOfBuiltinPredicates() {
        final Collection<FunctionSymbol> res = new ArrayList<FunctionSymbol>();
        res.add(PrologBuiltin.ABOLISH_PREDICATE);
        res.add(PrologBuiltin.CONJUNCTION_PREDICATE);
        res.add(PrologBuiltin.ARG_PREDICATE);
        res.add(PrologBuiltin.ASSERTA_PREDICATE);
        res.add(PrologBuiltin.ASSERTZ_PREDICATE);
        res.add(PrologBuiltin.AT_END_OF_STREAM_PREDICATE);
        res.add(PrologBuiltin.AT_END_OF_STREAM1_PREDICATE);
        res.add(PrologBuiltin.ATOM_CHARS_PREDICATE);
        res.add(PrologBuiltin.ATOM_CODES_PREDICATE);
        res.add(PrologBuiltin.ATOM_CONCAT_PREDICATE);
        res.add(PrologBuiltin.ATOM_LENGTH_PREDICATE);
        res.add(PrologBuiltin.ATOM_PREDICATE);
        res.add(PrologBuiltin.ATOMIC_PREDICATE);
        res.add(PrologBuiltin.BAGOF_PREDICATE);
        res.add(PrologBuiltin.CALL_PREDICATE);
        res.add(PrologBuiltin.CATCH_PREDICATE);
        res.add(PrologBuiltin.CHAR_CODE_PREDICATE);
        res.add(PrologBuiltin.CHAR_CONVERSION_PREDICATE);
        res.add(PrologBuiltin.CLAUSE_PREDICATE);
        res.add(PrologBuiltin.CLOSE_PREDICATE);
        res.add(PrologBuiltin.CLOSE2_PREDICATE);
        res.add(PrologBuiltin.COMPOUND_PREDICATE);
        res.add(PrologBuiltin.COPY_TERM_PREDICATE);
        res.add(PrologBuiltin.CURRENT_CHAR_CONVERSION_PREDICATE);
        res.add(PrologBuiltin.CURRENT_INPUT_PREDICATE);
        res.add(PrologBuiltin.CURRENT_OP_PREDICATE);
        res.add(PrologBuiltin.CURRENT_OUTPUT_PREDICATE);
        res.add(PrologBuiltin.CURRENT_PREDICATE_PREDICATE);
        res.add(PrologBuiltin.CURRENT_PROLOG_FLAG_PREDICATE);
        res.add(PrologBuiltin.CUT_PREDICATE);
        res.add(PrologBuiltin.EQUALS_PREDICATE);
        res.add(PrologBuiltin.FAIL_PREDICATE);
        res.add(PrologBuiltin.FINDALL_PREDICATE);
        res.add(PrologBuiltin.FLOAT_PREDICATE);
        res.add(PrologBuiltin.FLUSH_OUTPUT_PREDICATE);
        res.add(PrologBuiltin.FLUSH_OUTPUT1_PREDICATE);
        res.add(PrologBuiltin.FUNCTOR_PREDICATE);
        return res;
    }

    /**
     * @return The second 33% of all builtin predicates (because checkstyle moans if we add all at once...).
     */
    private static Collection<? extends FunctionSymbol> get2ndThirdOfBuiltinPredicates() {
        final Collection<FunctionSymbol> res = new ArrayList<FunctionSymbol>();
        res.add(PrologBuiltin.GEQ_PREDICATE);
        res.add(PrologBuiltin.GET_BYTE_PREDICATE);
        res.add(PrologBuiltin.GET_BYTE2_PREDICATE);
        res.add(PrologBuiltin.GET_CHAR_PREDICATE);
        res.add(PrologBuiltin.GET_CHAR2_PREDICATE);
        res.add(PrologBuiltin.GET_CODE_PREDICATE);
        res.add(PrologBuiltin.GET_CODE2_PREDICATE);
        res.add(PrologBuiltin.GREATER_PREDICATE);
        res.add(PrologBuiltin.HALT_PREDICATE);
        res.add(PrologBuiltin.HALT1_PREDICATE);
        res.add(PrologBuiltin.IF_PREDICATE);
        res.add(PrologBuiltin.INTEGER_PREDICATE);
        res.add(PrologBuiltin.IS_PREDICATE);
        res.add(PrologBuiltin.ISEQUAL_PREDICATE);
        res.add(PrologBuiltin.ISUNEQUAL_PREDICATE);
        res.add(PrologBuiltin.LEQ_PREDICATE);
        res.add(PrologBuiltin.LESS_PREDICATE);
        res.add(PrologBuiltin.LIST_CONSTRUCTOR_SYMBOL);
        res.add(PrologBuiltin.NEWLINE_PREDICATE);
        res.add(PrologBuiltin.NEWLINE1_PREDICATE);
        res.add(PrologBuiltin.NONVAR_PREDICATE);
        res.add(PrologBuiltin.NOT_PREDICATE);
        res.add(PrologBuiltin.NOUNIFY_PREDICATE);
        res.add(PrologBuiltin.NUMBER_CHARS_PREDICATE);
        res.add(PrologBuiltin.NUMBER_CODES_PREDICATE);
        res.add(PrologBuiltin.NUMBER_PREDICATE);
        res.add(PrologBuiltin.ONCE_PREDICATE);
        res.add(PrologBuiltin.OP_PREDICATE);
        res.add(PrologBuiltin.OPEN_PREDICATE);
        res.add(PrologBuiltin.OPEN4_PREDICATE);
        res.add(PrologBuiltin.DISJUNCTION_PREDICATE);
        return res;
    }

    /**
     * @return A collection of the six arithmetic comparison predicates in ISO Prolog.
     */
    private static Collection<FunctionSymbol> getArithmeticComparisonPredicates() {
        final Collection<FunctionSymbol> res = new ArrayList<FunctionSymbol>();
        res.add(PrologBuiltin.ISEQUAL_PREDICATE);
        res.add(PrologBuiltin.ISUNEQUAL_PREDICATE);
        res.add(PrologBuiltin.GEQ_PREDICATE);
        res.add(PrologBuiltin.GREATER_PREDICATE);
        res.add(PrologBuiltin.LEQ_PREDICATE);
        res.add(PrologBuiltin.LESS_PREDICATE);
        return res;
    }

    /**
     * @return A collection of operators which can be used in arithmetic expressions (e.g., +,-,*,...).
     */
    private static Collection<FunctionSymbol> getArithmeticOperators() {
        final Collection<FunctionSymbol> res = new ArrayList<FunctionSymbol>();
        res.add(PrologBuiltin.PLUS_SYMBOL);
        res.add(PrologBuiltin.MINUS_SYMBOL);
        res.add(PrologBuiltin.TIMES_SYMBOL);
        res.add(PrologBuiltin.INTDIV_SYMBOL);
        res.add(PrologBuiltin.DIV_SYMBOL);
        res.add(PrologBuiltin.POSITIVE_SIGN);
        res.add(PrologBuiltin.NEGATIVE_SIGN);
        res.add(PrologBuiltin.MODULO_SYMBOL);
        res.add(PrologBuiltin.INTPOWER_PREDICATE);
        //TODO more operators
        return res;
    }

    /**
     * @return A collection containing all built-in predicates according to the ISO standard.
     */
    private static Collection<FunctionSymbol> getBuiltinPredicates() {
        final Collection<FunctionSymbol> res = new ArrayList<FunctionSymbol>();
        res.addAll(PrologBuiltins.get1stThirdOfBuiltinPredicates());
        res.addAll(PrologBuiltins.get2ndThirdOfBuiltinPredicates());
        res.add(PrologBuiltin.PEEK_BYTE_PREDICATE);
        res.add(PrologBuiltin.PEEK_BYTE2_PREDICATE);
        res.add(PrologBuiltin.PEEK_CHAR_PREDICATE);
        res.add(PrologBuiltin.PEEK_CHAR2_PREDICATE);
        res.add(PrologBuiltin.PEEK_CODE_PREDICATE);
        res.add(PrologBuiltin.PEEK_CODE2_PREDICATE);
        res.add(PrologBuiltin.PUT_BYTE_PREDICATE);
        res.add(PrologBuiltin.PUT_BYTE2_PREDICATE);
        res.add(PrologBuiltin.PUT_CHAR_PREDICATE);
        res.add(PrologBuiltin.PUT_CHAR2_PREDICATE);
        res.add(PrologBuiltin.PUT_CODE_PREDICATE);
        res.add(PrologBuiltin.PUT_CODE2_PREDICATE);
        res.add(PrologBuiltin.READ_PREDICATE);
        res.add(PrologBuiltin.READ_TERM_PREDICATE);
        res.add(PrologBuiltin.READ_TERM3_PREDICATE);
        res.add(PrologBuiltin.READ2_PREDICATE);
        res.add(PrologBuiltin.REPEAT_PREDICATE);
        res.add(PrologBuiltin.RETRACT_PREDICATE);
        res.add(PrologBuiltin.SET_INPUT_PREDICATE);
        res.add(PrologBuiltin.SET_OUTPUT_PREDICATE);
        res.add(PrologBuiltin.SET_PROLOG_FLAG_PREDICATE);
        res.add(PrologBuiltin.SET_STREAM_POSITION_PREDICATE);
        res.add(PrologBuiltin.SETOF_PREDICATE);
        res.add(PrologBuiltin.STREAM_PROPERTY_PREDICATE);
        res.add(PrologBuiltin.SUB_ATOM_PREDICATE);
        res.add(PrologBuiltin.TERM_FOLLOWS_PREDICATE);
        res.add(PrologBuiltin.TERM_FOLLOWSEQ_PREDICATE);
        res.add(PrologBuiltin.TERM_PRECEDES_PREDICATE);
        res.add(PrologBuiltin.TERM_PRECEDESEQ_PREDICATE);
        res.add(PrologBuiltin.THROW_PREDICATE);
        res.add(PrologBuiltin.TRUE_PREDICATE);
        res.add(PrologBuiltin.UNEQUALS_PREDICATE);
        res.add(PrologBuiltin.UNIFY_PREDICATE);
        res.add(PrologBuiltin.UNIFY_WITH_OCCURS_CHECK_PREDICATE);
        res.add(PrologBuiltin.UNIV_PREDICATE);
        res.add(PrologBuiltin.VAR_PREDICATE);
        res.add(PrologBuiltin.WRITE_CANONICAL_PREDICATE);
        res.add(PrologBuiltin.WRITE_CANONICAL2_PREDICATE);
        res.add(PrologBuiltin.WRITE_PREDICATE);
        res.add(PrologBuiltin.WRITE_TERM_PREDICATE);
        res.add(PrologBuiltin.WRITE_TERM3_PREDICATE);
        res.add(PrologBuiltin.WRITE2_PREDICATE);
        res.add(PrologBuiltin.WRITEQ_PREDICATE);
        res.add(PrologBuiltin.WRITEQ2_PREDICATE);
        return res;
    }

    /**
     * @return A collection containing the names of all goal junctors (',', ';', and '->').
     */
    private static Collection<String> getGoalJunctorNames() {
        final Collection<String> res = new ArrayList<String>();
        res.add(PrologBuiltin.CONJUNCTION_NAME);
        res.add(PrologBuiltin.DISJUNCTION_NAME);
        res.add(PrologBuiltin.IF_NAME);
        return res;
    }

    /**
     * @return A collection containing the names of all goal junctors (',', ';', and '->').
     */
    private static Collection<FunctionSymbol> getGoalJunctors() {
        final Collection<FunctionSymbol> res = new ArrayList<FunctionSymbol>();
        res.add(PrologBuiltin.CONJUNCTION_PREDICATE);
        res.add(PrologBuiltin.DISJUNCTION_PREDICATE);
        res.add(PrologBuiltin.IF_PREDICATE);
        return res;
    }

    /**
     * @return A collection containing all built-in predicates using meta-calls.
     */
    private static Set<FunctionSymbol> getMetaBuiltinPredicates() {
        final Set<FunctionSymbol> res = new LinkedHashSet<FunctionSymbol>();
        res.add(PrologBuiltin.CONJUNCTION_PREDICATE);
        res.add(PrologBuiltin.CALL_PREDICATE);
        res.add(PrologBuiltin.IF_PREDICATE);
        res.add(PrologBuiltin.NOT_PREDICATE);
        res.add(PrologBuiltin.ONCE_PREDICATE);
        res.add(PrologBuiltin.DISJUNCTION_PREDICATE);
        return res;
    }

    /**
     * @return A collection containing all built-in predicate names according to the ISO standard.
     */
    private static Collection<String> getNamesOfBuiltinPredicates() {
        final Collection<String> res = new ArrayList<String>();
        res.addAll(PrologBuiltins.get1stHalfOfBuiltinPredicateNames());
        res.add(PrologBuiltin.LEQ_NAME);
        res.add(PrologBuiltin.LESS_NAME);
        res.add(PrologBuiltin.LIST_CONSTRUCTOR_NAME);
        res.add(PrologBuiltin.NEWLINE_NAME);
        res.add(PrologBuiltin.NONVAR_NAME);
        res.add(PrologBuiltin.NOT_NAME);
        res.add(PrologBuiltin.NOUNIFY_NAME);
        res.add(PrologBuiltin.NUMBER_CHARS_NAME);
        res.add(PrologBuiltin.NUMBER_CODES_NAME);
        res.add(PrologBuiltin.NUMBER_NAME);
        res.add(PrologBuiltin.ONCE_NAME);
        res.add(PrologBuiltin.OP_NAME);
        res.add(PrologBuiltin.OPEN_NAME);
        res.add(PrologBuiltin.DISJUNCTION_NAME);
        res.add(PrologBuiltin.PEEK_BYTE_NAME);
        res.add(PrologBuiltin.PEEK_CHAR_NAME);
        res.add(PrologBuiltin.PEEK_CODE_NAME);
        res.add(PrologBuiltin.PUT_BYTE_NAME);
        res.add(PrologBuiltin.PUT_CHAR_NAME);
        res.add(PrologBuiltin.PUT_CODE_NAME);
        res.add(PrologBuiltin.READ_NAME);
        res.add(PrologBuiltin.READ_TERM_NAME);
        res.add(PrologBuiltin.REPEAT_NAME);
        res.add(PrologBuiltin.RETRACT_NAME);
        res.add(PrologBuiltin.SET_INPUT_NAME);
        res.add(PrologBuiltin.SET_OUTPUT_NAME);
        res.add(PrologBuiltin.SET_PROLOG_FLAG_NAME);
        res.add(PrologBuiltin.SET_STREAM_POSITION_NAME);
        res.add(PrologBuiltin.SETOF_NAME);
        res.add(PrologBuiltin.STREAM_PROPERTY_NAME);
        res.add(PrologBuiltin.SUB_ATOM_NAME);
        res.add(PrologBuiltin.TERM_FOLLOWS_NAME);
        res.add(PrologBuiltin.TERM_FOLLOWSEQ_NAME);
        res.add(PrologBuiltin.TERM_PRECEDES_NAME);
        res.add(PrologBuiltin.TERM_PRECEDESEQ_NAME);
        res.add(PrologBuiltin.THROW_NAME);
        res.add(PrologBuiltin.TRUE_NAME);
        res.add(PrologBuiltin.UNEQUALS_NAME);
        res.add(PrologBuiltin.UNIFY_NAME);
        res.add(PrologBuiltin.UNIFY_WITH_OCCURS_CHECK_NAME);
        res.add(PrologBuiltin.UNIV_NAME);
        res.add(PrologBuiltin.VAR_NAME);
        res.add(PrologBuiltin.WRITE_CANONICAL_NAME);
        res.add(PrologBuiltin.WRITE_NAME);
        res.add(PrologBuiltin.WRITE_TERM_NAME);
        res.add(PrologBuiltin.WRITEQ_NAME);
        return res;
    }

    /**
     * @return A mapping from recursive built-in predicates to the number of resulting state elements without question
     *         marks.
     */
    private static Map<FunctionSymbol, Integer> getRecursiveBuiltinPredicates() {
        //TODO add further recursive built-ins
        final Map<FunctionSymbol, Integer> res = new LinkedHashMap<FunctionSymbol, Integer>();
        res.put(PrologBuiltin.REPEAT_PREDICATE, 2);
        return res;
    }

}
