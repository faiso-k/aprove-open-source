package aprove.verification.oldframework.Algebra.MinMaxExprs;

import static aprove.verification.oldframework.Algebra.MinMaxExprs.MinMaxExpr.*;

import java.math.*;
import java.text.*;
import java.util.*;

import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Parser for MinMaxExprs.
 * Does not support absolute values.
 * Unary minus is only supported if its argument is a natural number or a variable.
 */
public class MinMaxExprParser {

    /**
     * symbols that may occur in MinMaxExprs that we can parse
     */
    public enum Symbol {

        PLUS("+"),
        TIMES("*"),
        MINUS("-"),
        DIV("/"),
        COMMA(","),
        LBRACKET("("),
        RBRACKET(")"),
        LISTLBRACKET("["),
        LISTRBRACKET("]"),
        // there are infinitely many literals, so they don't have a string representation
        LITERAL(null),
        NAT("nat"),
        MIN("min"),
        MAX("max"),
        LOG("log");

        private String stringRepresentation;

        private Symbol(String s) {
            this.stringRepresentation = s;
        }

    }

    /**
     * thrown if the expression to parse contains the special value "inf" that represents infinity
     */
    @SuppressWarnings("serial")
    public static class InfiniteException extends Exception {}

    /*
     * reserved names that must not be interpreted as variables
     */
    private static List<String> reserved = new LinkedList<>(Arrays.asList(new String[]{"nat", "pow", "max", "min", "log", "inf"}));

    /*
     * just static methods, don't instantiate me
     */
    private MinMaxExprParser() {
    }

    /**
     * returns the length of the first token of "input"
     */
    private static int getTokenLength(String input) {
        int length = 1;
        int c = input.charAt(0);
        if (Character.isDigit(c)) {
            while (length < input.length()) {
                if (Character.isDigit(input.charAt(length))) {
                    length++;
                } else {
                    break;
                }
            }
        } else if (Character.isLetter(c)) {
            while (length < input.length()) {
                char d = input.charAt(length);
                if (Character.isLetter(d) || Character.isDigit(d) || d == '_' || d == '\'') {
                    length++;
                } else {
                    break;
                }
            }
        }
        return length;
    }

    /**
     * returns the first token of the argument
     */
    private static String getToken(String inputArg) throws InfiniteException {
        String input = inputArg.trim();
        if (input.isEmpty()) {
            return null;
        } else {
            int length = getTokenLength(input);
            String token = input.substring(0, length);
            if (token.equals("inf")) {
                throw new InfiniteException();
            }
            return token;
        }
    }

    /**
     * drops the first token of the argument
     */
    private static String dropToken(String inputArg) {
        String input = inputArg.trim();
        if (input.isEmpty()) {
            return input;
        } else {
            int length = getTokenLength(input);
            return input.substring(length);
        }
    }

    private static boolean isVariable(String token) {
        assert token.length() > 0;
        return Character.isLetter(token.charAt(0)) && !reserved.contains(token);
    }

    private static boolean isNumber(String token) {
        assert token.length() > 0;
        return Character.isDigit(token.charAt(0));
    }

    private static boolean match(Symbol sym, String token) {
        if (token == null) {
            return false;
        }
        switch (sym) {
            case LITERAL:
                return isNumber(token) || isVariable(token);
            default: return token.equals(sym.stringRepresentation);
        }
    }

    /**
     * parses a list of MinMaxExprs [p1,...,pn]
     * @param outer the function symbol above the list, e.g.,
     *              "max" if the whole input was "max([p1,...,pn])"
     * @return the remainder of the input and the parsed MinMaxExprs
     */
    private static Pair<String, Set<MinMaxExpr>> parseList(String inputArg, Symbol outer) throws ParseException, InfiniteException {
        String input = inputArg;
        String token = getToken(input);
        input = dropToken(input);
        assert(match(Symbol.LISTLBRACKET, token));
        Set<MinMaxExpr> res = new LinkedHashSet<>();
        while (true) {
            Pair<String, MinMaxExpr> p = doParse(input, outer);
            input = p.x;
            res.add(p.y);
            token = getToken(input);
            input = dropToken(input);
            if (match(Symbol.LISTRBRACKET, token)) {
                return new Pair<>(input, res);
            }
            assert match(Symbol.COMMA, token);
        }
    }

    public static MinMaxExpr parse(String input) throws ParseException, InfiniteException {
        return doParse(input, null).y.normalize();
    }

    /**
     * parses a MinMaxExpr
     * @param outer the outer function symbol, if any, e.g.,
     *              "*" if we are parsing the second argument of "p1 * p2"
     * @return the remainder of the input and the parsed MinMaxExpr
     */
    private static Pair<String, MinMaxExpr> doParse(String inputArg, Symbol outer) throws ParseException, InfiniteException {
        String input = inputArg;
        MinMaxExpr last = null;
        String token = getToken(input);
        input = dropToken(input);
        while (token != null) {
            if (isNumber(token)) {
                last = createInt(new BigInteger(token));
            } else if (isVariable(token)) {
                last = createVar(token);
            } else if (match(Symbol.MINUS, token)) {
                if (last == null) {
                    // unary minus
                    token = getToken(input);
                    input = dropToken(input);
                    assert isNumber(token) || isVariable(token) || match(Symbol.LBRACKET, token);
                    if (isNumber(token)) {
                        last = createInt(new BigInteger(token).negate());
                    } else if (isVariable(token)) {
                        last = createUnaryMinus(createVar(token));
                    } else if (match(Symbol.LBRACKET, token)) {
//                    	Negation of arbitrary MinMaxExpression
                    	Pair<String, MinMaxExpr> p = doParse(input, null);
                    	input = p.x;
                    	last = createUnaryMinus(p.y);
                    	token = getToken(input);
                    	input = dropToken(input);
                    	assert match(Symbol.RBRACKET, token);
                    }
                } else {
                    // subtraction
                    Pair<String, MinMaxExpr> p = doParse(input, Symbol.MINUS);
                    input = p.x;
                    last = createMinus(last, p.y);
                }
                
            } else if (match(Symbol.PLUS, token)) {
                Pair<String, MinMaxExpr> p = doParse(input, Symbol.PLUS);
                input = p.x;
                last = createPlus(last, p.y);
            } else if (match(Symbol.TIMES, token)) {
                Pair<String, MinMaxExpr> p = doParse(input, Symbol.TIMES);
                input = p.x;
                last = createTimes(last, p.y);
            } else if (match(Symbol.DIV, token)) {
                Pair<String, MinMaxExpr> p = doParse(input, Symbol.DIV);
                input = p.x;
                last = createDiv(last, p.y);
            } else if (match(Symbol.NAT, token)) {
                token = getToken(input);
                input = dropToken(input);
                assert match(Symbol.LBRACKET, token);
                Pair<String, MinMaxExpr> p = doParse(input, Symbol.NAT);
                input = p.x;
                last = createMax(p.y, createInt(BigInteger.ZERO));
                token = getToken(input);
                input = dropToken(input);
                assert match(Symbol.RBRACKET, token);
            } else if (match(Symbol.MAX, token)) {
                token = getToken(input);
                input = dropToken(input);
                assert match(Symbol.LBRACKET, token);
                Pair<String, Set<MinMaxExpr>> p = parseList(input, Symbol.MAX);
                input = p.x;
                last = createMax(p.y);
                token = getToken(input);
                input = dropToken(input);
                assert match(Symbol.RBRACKET, token);
            } else if (match(Symbol.MIN, token)) {
                token = getToken(input);
                input = dropToken(input);
                assert match(Symbol.LBRACKET, token);
                Pair<String, Set<MinMaxExpr>> p = parseList(input, Symbol.MIN);
                input = p.x;
                last = createMin(p.y);
                token = getToken(input);
                input = dropToken(input);
                assert match(Symbol.RBRACKET, token);
            } else if (match(Symbol.LOG, token)) {
                token = getToken(input);
                input = dropToken(input);
                assert match(Symbol.LBRACKET, token);
                Pair<String, MinMaxExpr> p = doParse(input, Symbol.LOG);
                input = p.x;
                MinMaxExpr base = p.y;
                token = getToken(input);
                input = dropToken(input);
                assert match(Symbol.COMMA, token);
                p = doParse(input, Symbol.LOG);
                input = p.x;
                MinMaxExpr arg = p.y;
                last = createLog(base, p.y);
                token = getToken(input);
                input = dropToken(input);
                assert match(Symbol.RBRACKET, token);
            } else if (match(Symbol.LBRACKET, token)) {
                Pair<String, MinMaxExpr> p = doParse(input, Symbol.LBRACKET);
                input = p.x;
                last = p.y;
                token = getToken(input);
                input = dropToken(input);
                assert match(Symbol.RBRACKET, token);
            } else {
                throw new ParseException(input, 0);
            }
            // check if we reached the end of a MinMaxExpr
            if (match(Symbol.RBRACKET, getToken(input)) || match(Symbol.COMMA, getToken(input)) || match(Symbol.LISTRBRACKET, getToken(input))) {
                return new Pair<>(input, last);
            }
            // handle precedences
            if (outer == Symbol.TIMES || outer == Symbol.DIV) {
                if (match(Symbol.PLUS, getToken(input)) || match(Symbol.MINUS, getToken(input)) || match(Symbol.TIMES, getToken(input)) || match(Symbol.DIV, getToken(input))) {
                    assert last != null;
                    return new Pair<>(input, last);
                }
            }
            if (outer == Symbol.PLUS || outer == Symbol.MINUS) {
                if (match(Symbol.PLUS, getToken(input)) || match(Symbol.MINUS, getToken(input))) {
                    assert last != null;
                    return new Pair<>(input, last);
                }
            }
            token = getToken(input);
            input = dropToken(input);
        }
        return new Pair<>(input, last);
    }

}
