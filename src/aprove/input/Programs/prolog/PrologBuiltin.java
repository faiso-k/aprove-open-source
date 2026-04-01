package aprove.input.Programs.prolog;

import aprove.verification.oldframework.BasicStructures.*;

/**
 * This class contains all built-in predicates according to the ISO standard
 * for Prolog.<br><br>
 *
 * Created: Oct 23, 2006<br>
 * Last modified: May 11, 2011
 *
 * @author cryingshadow
 * @version $Id$
 */
public abstract class PrologBuiltin {

    /**
     * The name of the abolish predicate.
     */
    public static final String ABOLISH_NAME = "abolish";

    /**
     * The abolish predicate with arity 1.
     */
    public static final FunctionSymbol ABOLISH_PREDICATE = FunctionSymbol.create(PrologBuiltin.ABOLISH_NAME, 1);

    /**
     * The name of the arg predicate.
     */
    public static final String ARG_NAME = "arg";

    /**
     * The arg predicate with arity 3.
     */
    public static final FunctionSymbol ARG_PREDICATE = FunctionSymbol.create(PrologBuiltin.ARG_NAME, 3);

    /**
     * The name of the asserta predicate.
     */
    public static final String ASSERTA_NAME = "asserta";

    /**
     * The asserta predicate with arity 1.
     */
    public static final FunctionSymbol ASSERTA_PREDICATE = FunctionSymbol.create(PrologBuiltin.ASSERTA_NAME, 1);

    /**
     * The name of the assertz predicate.
     */
    public static final String ASSERTZ_NAME = "assertz";

    /**
     * The assertz predicate with arity 1.
     */
    public static final FunctionSymbol ASSERTZ_PREDICATE = FunctionSymbol.create(PrologBuiltin.ASSERTZ_NAME, 1);

    /**
     * The name of the at_end_of_stream predicates.
     */
    public static final String AT_END_OF_STREAM_NAME = "at_end_of_stream";

    /**
     * The at_end_of_stream predicate with arity 0.
     */
    public static final FunctionSymbol AT_END_OF_STREAM_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.AT_END_OF_STREAM_NAME,
        0);

    /**
     * The at_end_of_stream predicate with arity 1.
     */
    public static final FunctionSymbol AT_END_OF_STREAM1_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.AT_END_OF_STREAM_NAME,
        1);

    /**
     * The name of the atom_chars predicate.
     */
    public static final String ATOM_CHARS_NAME = "atom_chars";

    /**
     * The atom_chars predicate with arity 2.
     */
    public static final FunctionSymbol ATOM_CHARS_PREDICATE = FunctionSymbol.create(PrologBuiltin.ATOM_CHARS_NAME, 2);

    /**
     * The name of the atom_codes predicate.
     */
    public static final String ATOM_CODES_NAME = "atom_codes";

    /**
     * The atom_codes predicate with arity 2.
     */
    public static final FunctionSymbol ATOM_CODES_PREDICATE = FunctionSymbol.create(PrologBuiltin.ATOM_CODES_NAME, 2);

    /**
     * The name of the atom_concat predicate.
     */
    public static final String ATOM_CONCAT_NAME = "atom_concat";

    /**
     * The atom_concat predicate with arity 3.
     */
    public static final FunctionSymbol ATOM_CONCAT_PREDICATE = FunctionSymbol.create(PrologBuiltin.ATOM_CONCAT_NAME, 3);

    /**
     * The name of the atom_length predicate.
     */
    public static final String ATOM_LENGTH_NAME = "atom_length";

    /**
     * The atom_length predicate with arity 2.
     */
    public static final FunctionSymbol ATOM_LENGTH_PREDICATE = FunctionSymbol.create(PrologBuiltin.ATOM_LENGTH_NAME, 2);

    /**
     * The name of the atom predicate.
     */
    public static final String ATOM_NAME = "atom";

    /**
     * The atom predicate with arity 1.
     */
    public static final FunctionSymbol ATOM_PREDICATE = FunctionSymbol.create(PrologBuiltin.ATOM_NAME, 1);

    /**
     * The name of the atomic predicate.
     */
    public static final String ATOMIC_NAME = "atomic";

    /**
     * The atomic predicate with arity 1.
     */
    public static final FunctionSymbol ATOMIC_PREDICATE = FunctionSymbol.create(PrologBuiltin.ATOMIC_NAME, 1);

    /**
     * The name of the bagof predicate.
     */
    public static final String BAGOF_NAME = "bagof";

    /**
     * The bagof predicate with arity 3.
     */
    public static final FunctionSymbol BAGOF_PREDICATE = FunctionSymbol.create(PrologBuiltin.BAGOF_NAME, 3);

    /**
     * The built-in predicate name call.
     */
    public static final String CALL_NAME = "call";

    /**
     * The built-in predicate call with arity 1.
     */
    public static final FunctionSymbol CALL_PREDICATE = FunctionSymbol.create(PrologBuiltin.CALL_NAME, 1);

    /**
     * The name of the catch predicate.
     */
    public static final String CATCH_NAME = "catch";

    /**
     * The catch predicate with arity 3.
     */
    public static final FunctionSymbol CATCH_PREDICATE = FunctionSymbol.create(PrologBuiltin.CATCH_NAME, 3);

    /**
     * The name of the char_code predicate.
     */
    public static final String CHAR_CODE_NAME = "char_code";

    /**
     * The char_code predicate with arity 2.
     */
    public static final FunctionSymbol CHAR_CODE_PREDICATE = FunctionSymbol.create(PrologBuiltin.CHAR_CODE_NAME, 2);

    /**
     * The name of the char_conversion predicate.
     */
    public static final String CHAR_CONVERSION_NAME = "char_conversion";

    /**
     * The char_conversion predicate with arity 2.
     */
    public static final FunctionSymbol CHAR_CONVERSION_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.CHAR_CONVERSION_NAME,
        2);

    /**
     * The name of the clause predicate.
     */
    public static final String CLAUSE_NAME = "clause";

    /**
     * The clause predicate with arity 2.
     */
    public static final FunctionSymbol CLAUSE_PREDICATE = FunctionSymbol.create(PrologBuiltin.CLAUSE_NAME, 2);

    /**
     * The name of the close predicates.
     */
    public static final String CLOSE_NAME = "close";

    /**
     * The close predicate with arity 1.
     */
    public static final FunctionSymbol CLOSE_PREDICATE = FunctionSymbol.create(PrologBuiltin.CLOSE_NAME, 1);

    /**
     * The close predicate with arity 2.
     */
    public static final FunctionSymbol CLOSE2_PREDICATE = FunctionSymbol.create(PrologBuiltin.CLOSE_NAME, 2);

    /**
     * The name of the compound predicate.
     */
    public static final String COMPOUND_NAME = "compound";

    /**
     * The compound predicate with arity 1.
     */
    public static final FunctionSymbol COMPOUND_PREDICATE = FunctionSymbol.create(PrologBuiltin.COMPOUND_NAME, 1);

    /**
     * The built in predicate name ','.
     */
    public static final String CONJUNCTION_NAME = "','";

    /**
     * The predicate ',' with arity 2.
     */
    public static final FunctionSymbol CONJUNCTION_PREDICATE = FunctionSymbol.create(PrologBuiltin.CONJUNCTION_NAME, 2);

    /**
     * The name of the copy_term predicate.
     */
    public static final String COPY_TERM_NAME = "copy_term";

    /**
     * The copy_term predicate with arity 2.
     */
    public static final FunctionSymbol COPY_TERM_PREDICATE = FunctionSymbol.create(PrologBuiltin.COPY_TERM_NAME, 2);

    /**
     * The name of the current_char_conversion predicate.
     */
    public static final String CURRENT_CHAR_CONVERSION_NAME = "current_char_conversion";

    /**
     * The current_char_conversion predicate with arity 2.
     */
    public static final FunctionSymbol CURRENT_CHAR_CONVERSION_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.CURRENT_CHAR_CONVERSION_NAME,
        2);

    /**
     * The name of the current_input predicate.
     */
    public static final String CURRENT_INPUT_NAME = "current_input";

    /**
     * The current_input predicate with arity 1.
     */
    public static final FunctionSymbol CURRENT_INPUT_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.CURRENT_INPUT_NAME,
        1);

    /**
     * The name of the current_op predicate.
     */
    public static final String CURRENT_OP_NAME = "current_op";

    /**
     * The current_op predicate with arity 3.
     */
    public static final FunctionSymbol CURRENT_OP_PREDICATE = FunctionSymbol.create(PrologBuiltin.CURRENT_OP_NAME, 3);

    /**
     * The name of the current_output predicate.
     */
    public static final String CURRENT_OUTPUT_NAME = "current_output";

    /**
     * The current_output predicate with arity 1.
     */
    public static final FunctionSymbol CURRENT_OUTPUT_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.CURRENT_OUTPUT_NAME,
        1);

    /**
     * The name of the current_predicate predicate.
     */
    public static final String CURRENT_PREDICATE_NAME = "current_predicate";

    /**
     * The current_predicate predicate with arity 1.
     */
    public static final FunctionSymbol CURRENT_PREDICATE_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.CURRENT_PREDICATE_NAME,
        1);

    /**
     * The name of the current_prolog_flag predicate.
     */
    public static final String CURRENT_PROLOG_FLAG_NAME = "current_prolog_flag";

    /**
     * The current_prolog_flag predicate with arity 2.
     */
    public static final FunctionSymbol CURRENT_PROLOG_FLAG_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.CURRENT_PROLOG_FLAG_NAME,
        2);

    /**
     * The built in predicate name !.
     */
    public static final String CUT_NAME = "!";

    /**
     * The predicate ! with arity 0.
     */
    public static final FunctionSymbol CUT_PREDICATE = FunctionSymbol.create(PrologBuiltin.CUT_NAME, 0);

    /**
     * The built in predicate name ;.
     */
    public static final String DISJUNCTION_NAME = ";";

    /**
     * The predicate ; with arity 2.
     */
    public static final FunctionSymbol DISJUNCTION_PREDICATE = FunctionSymbol.create(PrologBuiltin.DISJUNCTION_NAME, 2);

    /**
     * The name of the division operator.
     */
    public static final String DIV_NAME = "/";

    /**
     * The division operator with arity 2.
     */
    public static final FunctionSymbol DIV_SYMBOL = FunctionSymbol.create(PrologBuiltin.DIV_NAME, 2);

    /**
     * The name of the empty list constructor ([]).
     */
    public static final String EMPTY_LIST_CONSTRUCTOR_NAME = "[]";

    /**
     * The empty list constructor ([]) with arity 0.
     */
    public static final FunctionSymbol EMPTY_LIST_CONSTRUCTOR_SYMBOL = FunctionSymbol.create(
        PrologBuiltin.EMPTY_LIST_CONSTRUCTOR_NAME,
        0);

    /**
     * The built in predicate name ==.
     */
    public static final String EQUALS_NAME = "==";

    /**
     * The predicate == with arity 2.
     */
    public static final FunctionSymbol EQUALS_PREDICATE = FunctionSymbol.create(PrologBuiltin.EQUALS_NAME, 2);

    /**
     * The built in predicate name fail.
     */
    public static final String FAIL_NAME = "fail";

    /**
     * The predicate fail with arity 0.
     */
    public static final FunctionSymbol FAIL_PREDICATE = FunctionSymbol.create(PrologBuiltin.FAIL_NAME, 0);

    /**
     * The name of the findall predicate.
     */
    public static final String FINDALL_NAME = "findall";

    /**
     * The findall predicate with arity 3.
     */
    public static final FunctionSymbol FINDALL_PREDICATE = FunctionSymbol.create(PrologBuiltin.FINDALL_NAME, 3);

    /**
     * The name of the float predicate.
     */
    public static final String FLOAT_NAME = "float";

    /**
     * The float predicate with arity 1.
     */
    public static final FunctionSymbol FLOAT_PREDICATE = FunctionSymbol.create(PrologBuiltin.FLOAT_NAME, 1);

    /**
     * The name of the flush_output predicates.
     */
    public static final String FLUSH_OUTPUT_NAME = "flush_output";

    /**
     * The flush_output predicate with arity 0.
     */
    public static final FunctionSymbol FLUSH_OUTPUT_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.FLUSH_OUTPUT_NAME,
        0);

    /**
     * The flush_output predicate with arity 1.
     */
    public static final FunctionSymbol FLUSH_OUTPUT1_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.FLUSH_OUTPUT_NAME,
        1);

    /**
     * The name of the functor predicate.
     */
    public static final String FUNCTOR_NAME = "functor";

    /**
     * The functor predicate with arity 3.
     */
    public static final FunctionSymbol FUNCTOR_PREDICATE = FunctionSymbol.create(PrologBuiltin.FUNCTOR_NAME, 3);

    /**
     * The built in predicate name >=.
     */
    public static final String GEQ_NAME = ">=";

    /**
     * The predicate >= with arity 2.
     */
    public static final FunctionSymbol GEQ_PREDICATE = FunctionSymbol.create(PrologBuiltin.GEQ_NAME, 2);

    /**
     * The name of the get_byte predicates.
     */
    public static final String GET_BYTE_NAME = "get_byte";

    /**
     * The get_byte predicate with arity 1.
     */
    public static final FunctionSymbol GET_BYTE_PREDICATE = FunctionSymbol.create(PrologBuiltin.GET_BYTE_NAME, 1);

    /**
     * The get_byte predicate with arity 2.
     */
    public static final FunctionSymbol GET_BYTE2_PREDICATE = FunctionSymbol.create(PrologBuiltin.GET_BYTE_NAME, 2);

    /**
     * The name of the get_char predicates.
     */
    public static final String GET_CHAR_NAME = "get_char";

    /**
     * The get_char predicate with arity 1.
     */
    public static final FunctionSymbol GET_CHAR_PREDICATE = FunctionSymbol.create(PrologBuiltin.GET_CHAR_NAME, 1);

    /**
     * The get_char predicate with arity 2.
     */
    public static final FunctionSymbol GET_CHAR2_PREDICATE = FunctionSymbol.create(PrologBuiltin.GET_CHAR_NAME, 2);

    /**
     * The name of the get_code predicates.
     */
    public static final String GET_CODE_NAME = "get_code";

    /**
     * The get_code predicate with arity 1.
     */
    public static final FunctionSymbol GET_CODE_PREDICATE = FunctionSymbol.create(PrologBuiltin.GET_CODE_NAME, 1);

    /**
     * The get_code predicate with arity 2.
     */
    public static final FunctionSymbol GET_CODE2_PREDICATE = FunctionSymbol.create(PrologBuiltin.GET_CODE_NAME, 2);

    /**
     * The built in predicate name >.
     */
    public static final String GREATER_NAME = ">";

    /**
     * The predicate > with arity 2.
     */
    public static final FunctionSymbol GREATER_PREDICATE = FunctionSymbol.create(PrologBuiltin.GREATER_NAME, 2);

    /**
     * The name of the halt predicates.
     */
    public static final String HALT_NAME = "halt";

    /**
     * The halt predicate with arity 0.
     */
    public static final FunctionSymbol HALT_PREDICATE = FunctionSymbol.create(PrologBuiltin.HALT_NAME, 0);

    /**
     * The halt predicate with arity 1.
     */
    public static final FunctionSymbol HALT1_PREDICATE = FunctionSymbol.create(PrologBuiltin.HALT_NAME, 1);

    /**
     * The built in predicate name ->.
     */
    public static final String IF_NAME = "->";

    /**
     * The predicate -> with arity 2.
     */
    public static final FunctionSymbol IF_PREDICATE = FunctionSymbol.create(PrologBuiltin.IF_NAME, 2);

    /**
     * The name of the operator for integer division.
     */
    public static final String INTDIV_NAME = "//";

    /**
     * The operator for integer division with arity 2.
     */
    public static final FunctionSymbol INTDIV_SYMBOL = FunctionSymbol.create(PrologBuiltin.INTDIV_NAME, 2);

    /**
     * The name of the integer predicate.
     */
    public static final String INTEGER_NAME = "integer";

    /**
     * The integer predicate with arity 1.
     */
    public static final FunctionSymbol INTEGER_PREDICATE = FunctionSymbol.create(PrologBuiltin.INTEGER_NAME, 1);

    /**
     * The name of the integer power operator.
     */
    public static final String INTPOWER_NAME = "^";

    /**
     * The integer power predicate with arity 2.
     */
    public static final FunctionSymbol INTPOWER_PREDICATE = FunctionSymbol.create(PrologBuiltin.INTPOWER_NAME, 2);

    /**
     * The built in predicate name is.
     */
    public static final String IS_NAME = "is";

    /**
     * The predicate is with arity 2.
     */
    public static final FunctionSymbol IS_PREDICATE = FunctionSymbol.create(PrologBuiltin.IS_NAME, 2);

    /**
     * The built in predicate name =:=.
     */
    public static final String ISEQUAL_NAME = "=:=";

    /**
     * The predicate =:= with arity 2.
     */
    public static final FunctionSymbol ISEQUAL_PREDICATE = FunctionSymbol.create(PrologBuiltin.ISEQUAL_NAME, 2);

    /**
     * The built in predicate name =\=.
     */
    public static final String ISUNEQUAL_NAME = "=\\=";

    /**
     * The predicate =\= with arity 2.
     */
    public static final FunctionSymbol ISUNEQUAL_PREDICATE = FunctionSymbol.create(PrologBuiltin.ISUNEQUAL_NAME, 2);

    /**
     * The built in predicate name =<.
     */
    public static final String LEQ_NAME = "=<";

    /**
     * The predicate =< with arity 2.
     */
    public static final FunctionSymbol LEQ_PREDICATE = FunctionSymbol.create(PrologBuiltin.LEQ_NAME, 2);

    /**
     * The built in predicate name <.
     */
    public static final String LESS_NAME = "<";

    /**
     * The predicate < with arity 2.
     */
    public static final FunctionSymbol LESS_PREDICATE = FunctionSymbol.create(PrologBuiltin.LESS_NAME, 2);

    /**
     * The built in name for the list constructor (.).
     */
    public static final String LIST_CONSTRUCTOR_NAME = ".";

    /**
     * The list constructor (.) with arity 2.
     */
    public static final FunctionSymbol LIST_CONSTRUCTOR_SYMBOL = FunctionSymbol.create(
        PrologBuiltin.LIST_CONSTRUCTOR_NAME,
        2);

    /**
     * The name of the minus operator or the negative sign.
     */
    public static final String MINUS_NAME = "-";

    /**
     * The minus operator with arity 2.
     */
    public static final FunctionSymbol MINUS_SYMBOL = FunctionSymbol.create(PrologBuiltin.MINUS_NAME, 2);

    /**
     * The name of the modulo operator
     */
    public static final String MODULO_NAME = "mod";

    /**
     * The modulo operator with arity 2.
     */
    public static final FunctionSymbol MODULO_SYMBOL = FunctionSymbol.create(PrologBuiltin.MODULO_NAME, 2);

    /**
     * The negative sign with arity 1.
     */
    public static final FunctionSymbol NEGATIVE_SIGN = FunctionSymbol.create(PrologBuiltin.MINUS_NAME, 1);

    /**
     * The name of the nl predicates.
     */
    public static final String NEWLINE_NAME = "nl";

    /**
     * The nl predicate with arity 0.
     */
    public static final FunctionSymbol NEWLINE_PREDICATE = FunctionSymbol.create(PrologBuiltin.NEWLINE_NAME, 0);

    /**
     * The nl predicate with arity 1.
     */
    public static final FunctionSymbol NEWLINE1_PREDICATE = FunctionSymbol.create(PrologBuiltin.NEWLINE_NAME, 1);

    /**
     * The name of the nonvar predicate.
     */
    public static final String NONVAR_NAME = "nonvar";

    /**
     * The nonvar predicate with arity 1.
     */
    public static final FunctionSymbol NONVAR_PREDICATE = FunctionSymbol.create(PrologBuiltin.NONVAR_NAME, 1);

    /**
     * The built in predicate name \+.
     */
    public static final String NOT_NAME = "\\+";

    /**
     * The predicate \+ with arity 1.
     */
    public static final FunctionSymbol NOT_PREDICATE = FunctionSymbol.create(PrologBuiltin.NOT_NAME, 1);

    /**
     * The name of the nounify predicate (\=).
     */
    public static final String NOUNIFY_NAME = "\\=";

    /**
     * The nounify predicate (\=) with arity 2.
     */
    public static final FunctionSymbol NOUNIFY_PREDICATE = FunctionSymbol.create(PrologBuiltin.NOUNIFY_NAME, 2);

    /**
     * The name of the number_chars predicate.
     */
    public static final String NUMBER_CHARS_NAME = "number_chars";

    /**
     * The number_chars predicate with arity 2.
     */
    public static final FunctionSymbol NUMBER_CHARS_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.NUMBER_CHARS_NAME,
        2);

    /**
     * The name of the number_codes predicate.
     */
    public static final String NUMBER_CODES_NAME = "number_codes";

    /**
     * The number_codes predicate with arity 2.
     */
    public static final FunctionSymbol NUMBER_CODES_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.NUMBER_CODES_NAME,
        2);

    /**
     * The name of the number predicate.
     */
    public static final String NUMBER_NAME = "number";

    /**
     * The number predicate with arity 1.
     */
    public static final FunctionSymbol NUMBER_PREDICATE = FunctionSymbol.create(PrologBuiltin.NUMBER_NAME, 1);

    /**
     * The name of the once predicate.
     */
    public static final String ONCE_NAME = "once";

    /**
     * The once predicate with arity 1.
     */
    public static final FunctionSymbol ONCE_PREDICATE = FunctionSymbol.create(PrologBuiltin.ONCE_NAME, 1);

    /**
     * The name of the op predicate.
     */
    public static final String OP_NAME = "op";

    /**
     * The op predicate with arity 3.
     */
    public static final FunctionSymbol OP_PREDICATE = FunctionSymbol.create(PrologBuiltin.OP_NAME, 3);

    /**
     * The name of the open predicates.
     */
    public static final String OPEN_NAME = "open";

    /**
     * The open predicate with arity 3.
     */
    public static final FunctionSymbol OPEN_PREDICATE = FunctionSymbol.create(PrologBuiltin.OPEN_NAME, 3);

    /**
     * The open predicate with arity 4.
     */
    public static final FunctionSymbol OPEN4_PREDICATE = FunctionSymbol.create(PrologBuiltin.OPEN_NAME, 4);

    /**
     * The name of the peek_byte predicates.
     */
    public static final String PEEK_BYTE_NAME = "peek_byte";

    /**
     * The peek_byte predicate with arity 1.
     */
    public static final FunctionSymbol PEEK_BYTE_PREDICATE = FunctionSymbol.create(PrologBuiltin.PEEK_BYTE_NAME, 1);

    /**
     * The peek_byte predicate with arity 2.
     */
    public static final FunctionSymbol PEEK_BYTE2_PREDICATE = FunctionSymbol.create(PrologBuiltin.PEEK_BYTE_NAME, 2);

    /**
     * The name of the peek_char predicates.
     */
    public static final String PEEK_CHAR_NAME = "peek_char";

    /**
     * The peek_char predicate with arity 1.
     */
    public static final FunctionSymbol PEEK_CHAR_PREDICATE = FunctionSymbol.create(PrologBuiltin.PEEK_CHAR_NAME, 1);

    /**
     * The peek_char predicate with arity 2.
     */
    public static final FunctionSymbol PEEK_CHAR2_PREDICATE = FunctionSymbol.create(PrologBuiltin.PEEK_CHAR_NAME, 2);

    /**
     * The name of the peek_code predicates.
     */
    public static final String PEEK_CODE_NAME = "peek_code";

    /**
     * The peek_code predicate with arity 1.
     */
    public static final FunctionSymbol PEEK_CODE_PREDICATE = FunctionSymbol.create(PrologBuiltin.PEEK_CODE_NAME, 1);

    /**
     * The peek_code predicate with arity 2.
     */
    public static final FunctionSymbol PEEK_CODE2_PREDICATE = FunctionSymbol.create(PrologBuiltin.PEEK_CODE_NAME, 2);

    /**
     * The name of the plus operator or the positive sign.
     */
    public static final String PLUS_NAME = "+";

    /**
     * The plus operator with arity 2.
     */
    public static final FunctionSymbol PLUS_SYMBOL = FunctionSymbol.create(PrologBuiltin.PLUS_NAME, 2);

    /**
     * The positive sign with arity 1.
     */
    public static final FunctionSymbol POSITIVE_SIGN = FunctionSymbol.create(PrologBuiltin.PLUS_NAME, 1);

    /**
     * The name of the put_byte predicates.
     */
    public static final String PUT_BYTE_NAME = "put_byte";

    /**
     * The put_byte predicate with arity 1.
     */
    public static final FunctionSymbol PUT_BYTE_PREDICATE = FunctionSymbol.create(PrologBuiltin.PUT_BYTE_NAME, 1);

    /**
     * The put_byte predicate with arity 2.
     */
    public static final FunctionSymbol PUT_BYTE2_PREDICATE = FunctionSymbol.create(PrologBuiltin.PUT_BYTE_NAME, 2);

    /**
     * The name of the put_char predicates.
     */
    public static final String PUT_CHAR_NAME = "put_char";

    /**
     * The put_char predicate with arity 1.
     */
    public static final FunctionSymbol PUT_CHAR_PREDICATE = FunctionSymbol.create(PrologBuiltin.PUT_CHAR_NAME, 1);

    /**
     * The put_char predicate with arity 2.
     */
    public static final FunctionSymbol PUT_CHAR2_PREDICATE = FunctionSymbol.create(PrologBuiltin.PUT_CHAR_NAME, 2);

    /**
     * The name of the put_code predicates.
     */
    public static final String PUT_CODE_NAME = "put_code";

    /**
     * The put_code predicate with arity 1.
     */
    public static final FunctionSymbol PUT_CODE_PREDICATE = FunctionSymbol.create(PrologBuiltin.PUT_CODE_NAME, 1);

    /**
     * The put_code predicate with arity 2.
     */
    public static final FunctionSymbol PUT_CODE2_PREDICATE = FunctionSymbol.create(PrologBuiltin.PUT_CODE_NAME, 2);

    /**
     * The name of the read predicates.
     */
    public static final String READ_NAME = "read";

    /**
     * The read predicate with arity 1.
     */
    public static final FunctionSymbol READ_PREDICATE = FunctionSymbol.create(PrologBuiltin.READ_NAME, 1);

    /**
     * The name of the read_term predicates.
     */
    public static final String READ_TERM_NAME = "read_term";

    /**
     * The read_term predicate with arity 2.
     */
    public static final FunctionSymbol READ_TERM_PREDICATE = FunctionSymbol.create(PrologBuiltin.READ_TERM_NAME, 2);

    /**
     * The read_term predicate with arity 3.
     */
    public static final FunctionSymbol READ_TERM3_PREDICATE = FunctionSymbol.create(PrologBuiltin.READ_TERM_NAME, 3);

    /**
     * The read predicate with arity 2.
     */
    public static final FunctionSymbol READ2_PREDICATE = FunctionSymbol.create(PrologBuiltin.READ_NAME, 2);

    /**
     * The name of the repeat predicate.
     */
    public static final String REPEAT_NAME = "repeat";

    /**
     * The repeat predicate with arity 0.
     */
    public static final FunctionSymbol REPEAT_PREDICATE = FunctionSymbol.create(PrologBuiltin.REPEAT_NAME, 0);

    /**
     * The name of the retract predicate.
     */
    public static final String RETRACT_NAME = "retract";

    /**
     * The retract predicate with arity 1.
     */
    public static final FunctionSymbol RETRACT_PREDICATE = FunctionSymbol.create(PrologBuiltin.RETRACT_NAME, 1);

    /**
     * The name of the set_input predicate.
     */
    public static final String SET_INPUT_NAME = "set_input";

    /**
     * The set_input predicate with arity 1.
     */
    public static final FunctionSymbol SET_INPUT_PREDICATE = FunctionSymbol.create(PrologBuiltin.SET_INPUT_NAME, 1);

    /**
     * The name of the set_output predicate.
     */
    public static final String SET_OUTPUT_NAME = "set_output";

    /**
     * The set_output predicate with arity 1.
     */
    public static final FunctionSymbol SET_OUTPUT_PREDICATE = FunctionSymbol.create(PrologBuiltin.SET_OUTPUT_NAME, 1);

    /**
     * The name of the set_prolog_flag predicate.
     */
    public static final String SET_PROLOG_FLAG_NAME = "set_prolog_flag";

    /**
     * The set_prolog_flag predicate with arity 2.
     */
    public static final FunctionSymbol SET_PROLOG_FLAG_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.SET_PROLOG_FLAG_NAME,
        2);

    /**
     * The name of the set_stream_position predicate.
     */
    public static final String SET_STREAM_POSITION_NAME = "set_stream_position";

    /**
     * The set_stream_position predicate with arity 2.
     */
    public static final FunctionSymbol SET_STREAM_POSITION_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.SET_STREAM_POSITION_NAME,
        2);

    /**
     * The name of the setof predicate.
     */
    public static final String SETOF_NAME = "setof";

    /**
     * The setof predicate with arity 3.
     */
    public static final FunctionSymbol SETOF_PREDICATE = FunctionSymbol.create(PrologBuiltin.SETOF_NAME, 3);

    /**
     * The name of the stream_property predicate.
     */
    public static final String STREAM_PROPERTY_NAME = "stream_property";

    /**
     * The stream_property predicate with arity 2.
     */
    public static final FunctionSymbol STREAM_PROPERTY_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.STREAM_PROPERTY_NAME,
        2);

    /**
     * The name of the sub_atom predicate.
     */
    public static final String SUB_ATOM_NAME = "sub_atom";

    /**
     * The sub_atom predicate with arity 5.
     */
    public static final FunctionSymbol SUB_ATOM_PREDICATE = FunctionSymbol.create(PrologBuiltin.SUB_ATOM_NAME, 5);

    /**
     * The name of the term_follows predicate (@>).
     */
    public static final String TERM_FOLLOWS_NAME = "@>";

    /**
     * The term_follows predicate (@>) with arity 2.
     */
    public static final FunctionSymbol TERM_FOLLOWS_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.TERM_FOLLOWS_NAME,
        2);

    /**
     * The name of the term_followseq predicate (@>=).
     */
    public static final String TERM_FOLLOWSEQ_NAME = "@>=";

    /**
     * The term_followseq predicate (@>=) with arity 2.
     */
    public static final FunctionSymbol TERM_FOLLOWSEQ_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.TERM_FOLLOWSEQ_NAME,
        2);

    /**
     * The name of the term_precedes predicate (@<).
     */
    public static final String TERM_PRECEDES_NAME = "@<";

    /**
     * The term_precedes predicate (@<) with arity 2.
     */
    public static final FunctionSymbol TERM_PRECEDES_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.TERM_PRECEDES_NAME,
        2);

    /**
     * The name of the term_precedeseq predicate (@=<).
     */
    public static final String TERM_PRECEDESEQ_NAME = "@=<";

    /**
     * The term_precedeseq predicate (@=<) with arity 2.
     */
    public static final FunctionSymbol TERM_PRECEDESEQ_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.TERM_PRECEDESEQ_NAME,
        2);

    /**
     * The name of the throw predicate.
     */
    public static final String THROW_NAME = "throw";

    /**
     * The throw predicate with arity 1.
     */
    public static final FunctionSymbol THROW_PREDICATE = FunctionSymbol.create(PrologBuiltin.THROW_NAME, 1);

    /**
     * The name of the times operator.
     */
    public static final String TIMES_NAME = "*";

    /**
     * The times operator with arity 2.
     */
    public static final FunctionSymbol TIMES_SYMBOL = FunctionSymbol.create(PrologBuiltin.TIMES_NAME, 2);

    /**
     * The built in predicate name true.
     */
    public static final String TRUE_NAME = "true";

    /**
     * The predicate true with arity 0.
     */
    public static final FunctionSymbol TRUE_PREDICATE = FunctionSymbol.create(PrologBuiltin.TRUE_NAME, 0);

    /**
     * The name of the unequals predicate (\==).
     */
    public static final String UNEQUALS_NAME = "\\==";

    /**
     * The unequals predicate (\==) with arity 2.
     */
    public static final FunctionSymbol UNEQUALS_PREDICATE = FunctionSymbol.create(PrologBuiltin.UNEQUALS_NAME, 2);

    /**
     * The name of the unify predicate (=).
     */
    public static final String UNIFY_NAME = "=";

    /**
     * The unify predicate (=) with arity 2.
     */
    public static final FunctionSymbol UNIFY_PREDICATE = FunctionSymbol.create(PrologBuiltin.UNIFY_NAME, 2);

    /**
     * The name of the unify_with_occurs_check predicate.
     */
    public static final String UNIFY_WITH_OCCURS_CHECK_NAME = "unify_with_occurs_check";

    /**
     * The unify_with_occurs_check predicate with arity 2.
     */
    public static final FunctionSymbol UNIFY_WITH_OCCURS_CHECK_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.UNIFY_WITH_OCCURS_CHECK_NAME,
        2);

    /**
     * The name of the univ predicate (=..).
     */
    public static final String UNIV_NAME = "=..";

    /**
     * The univ predicate (=..) with arity 2.
     */
    public static final FunctionSymbol UNIV_PREDICATE = FunctionSymbol.create(PrologBuiltin.UNIV_NAME, 2);

    /**
     * The name of the var predicate.
     */
    public static final String VAR_NAME = "var";

    /**
     * The var predicate with arity 1.
     */
    public static final FunctionSymbol VAR_PREDICATE = FunctionSymbol.create(PrologBuiltin.VAR_NAME, 1);

    /**
     * The name of the write_canonical predicates.
     */
    public static final String WRITE_CANONICAL_NAME = "write_canonical";

    /**
     * The write_canonical predicate with arity 1.
     */
    public static final FunctionSymbol WRITE_CANONICAL_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.WRITE_CANONICAL_NAME,
        1);

    /**
     * The write_canonical predicate with arity 2.
     */
    public static final FunctionSymbol WRITE_CANONICAL2_PREDICATE = FunctionSymbol.create(
        PrologBuiltin.WRITE_CANONICAL_NAME,
        2);

    /**
     * The name of the write predicates.
     */
    public static final String WRITE_NAME = "write";

    /**
     * The write predicate with arity 1.
     */
    public static final FunctionSymbol WRITE_PREDICATE = FunctionSymbol.create(PrologBuiltin.WRITE_NAME, 1);

    /**
     * The name of the write_term predicates.
     */
    public static final String WRITE_TERM_NAME = "write_term";

    /**
     * The write_term predicate with arity 2.
     */
    public static final FunctionSymbol WRITE_TERM_PREDICATE = FunctionSymbol.create(PrologBuiltin.WRITE_TERM_NAME, 2);

    /**
     * The write_term predicate with arity 3.
     */
    public static final FunctionSymbol WRITE_TERM3_PREDICATE = FunctionSymbol.create(PrologBuiltin.WRITE_TERM_NAME, 3);

    /**
     * The write predicate with arity 2.
     */
    public static final FunctionSymbol WRITE2_PREDICATE = FunctionSymbol.create(PrologBuiltin.WRITE_NAME, 2);

    /**
     * The name of the writeq predicates.
     */
    public static final String WRITEQ_NAME = "writeq";

    /**
     * The writeq predicate with arity 1.
     */
    public static final FunctionSymbol WRITEQ_PREDICATE = FunctionSymbol.create(PrologBuiltin.WRITEQ_NAME, 1);

    /**
     * The writeq predicate with arity 2.
     */
    public static final FunctionSymbol WRITEQ2_PREDICATE = FunctionSymbol.create(PrologBuiltin.WRITEQ_NAME, 2);

    /**
     * Hides the default constructor.
     */
    private PrologBuiltin() {
        // no object
    }

}
