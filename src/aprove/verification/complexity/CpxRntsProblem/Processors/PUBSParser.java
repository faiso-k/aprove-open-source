package aprove.verification.complexity.CpxRntsProblem.Processors;

import static aprove.verification.complexity.CpxRntsProblem.Processors.PUBSParser.Symbol.*;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * Parse PUBS complexity value and polynomial, mostly stolen from CpxIntTrsProblem.KoATParser.
 * Additionally supports max, log, minus (which is interpreted as plus).
 *
 * SUM       -> PROD SUM_CONT
 * SUM_CONT  -> +/- PROD SUM_MARKER SUM_CONT | eps
 * PROD      -> POW PROD_CONT
 * PROD_CONT -> * / POW PROD_MARKER PROD_CONT | eps
 * POW       -> EXPR POW_CONT | pow ( SUM , SUM ) POW_MARKER
 * POW_CONT  -> ^ EXPR POW_MARKER | eps
 * LIST      -> SUM LIST_CONT
 * LIST_CONT -> , SUM LIST_MARKER LIST_CONT | eps
 * EXPR      -> ( SUM ) | lit | nat ( SUM ) NAT_MARKER | - EXPR
 *              | max ( [ LIST ] ) MAX_MARKER
 *              | log ( SUM , SUM ) LOG_MARKER
 *
 * @author mnaaf, mostly stolen from KoATParser
 *
 */
public class PUBSParser {

    @SuppressWarnings("serial")
    private static class ParserException extends RuntimeException {}

    public enum Symbol {
        SUM, SUM_CONT, PLUS, SUM_MARKER,
        PROD, PROD_CONT, DOT, PROD_MARKER, SLASH, DIV_MARKER,
        POW, POW_CONT, CARET, POW_SYM, KOMA, POW_MARKER,
        LOG_SYM, LOG_MARKER, LIST, LIST_CONT, LIST_MARKER,
        EXPR, LBRACKET, RBRACKET, LISTLBRACKET, LISTRBRACKET,
        LITERAL, NAT_SYM, NAT_MARKER,
        MAX_SYM, MAX_MARKER, UNARY_MINUS
    }

    private static List<String> reserved = new LinkedList<>
        (Arrays.asList(new String[]{"nat", "pow", "max", "log"}));

    private static abstract class SyntaxTree {}

    private static class Number extends SyntaxTree implements Comparable<Number> {

        public static final Number ONE = new Number(BigInteger.ONE);

        BigInteger value;

        public Number(String token) {
            this.value = new BigInteger(token);
        }

        public Number(BigInteger value) {
            this.value = value;
        }

        @Override
        public String toString() {
            return value.toString();
        }

        @Override
        public int compareTo(Number that) {
            return this.value.compareTo(that.value);
        }
    }

    private static class TRSVariable extends SyntaxTree {
        String name;

        public TRSVariable(String token) {
            this.name = token;
        }

        @Override
        public String toString() {
            return name;
        }
    }

    private static class Op extends SyntaxTree {
        SyntaxTree left, right;
        Symbol operation;

        public Op(Symbol operation, SyntaxTree left, SyntaxTree right) {
            this.operation = operation;
            this.left = left;
            this.right = right;
        }

        @Override
        public String toString() {
            switch (operation) {
                case SUM_MARKER:
                    return "(" + left + " + " + right + ")";
                case PROD_MARKER:
                    return "(" + left + " * " + right + ")";
                case DIV_MARKER:
                    return "(" + left + " / " + right + ")";
                case POW_MARKER:
                    return "(" + left + " ^ " + right + ")";
                case MAX_MARKER:
                    return "max(" + left + "," + right + ")";
                case LOG_MARKER:
                    return "log(" + left + "," + right + ")";
                default:
                    throw new RuntimeException();
            }
        }
    }

    private String input;
    private String token;

    private int index;

    private LinkedList<Symbol> symbolStack;
    private LinkedList<SyntaxTree> syntaxStack;

    private PUBSParser(String input) {
        this.input = input;
        this.token = getToken();

        this.symbolStack = new LinkedList<Symbol>();
        this.syntaxStack = new LinkedList<SyntaxTree>();
    }

    /**
     * Check if current token is a number.
     */
    private boolean isNumber() {
        assert this.token.length() > 0;
        return Character.isDigit(this.token.charAt(0));
    }

    /**
     * Check if current token is a variable.
     */
    private boolean isVariable() {
        assert this.token.length() > 0;
        return Character.isLetter(this.token.charAt(0)) && !reserved.contains(this.token);
    }

    /**
     * Check if the current token matches the given grammar symbol.
     */
    private boolean match(Symbol sym) {

        if (this.token == null) {
            return false;
        }

        switch (sym) {
            case UNARY_MINUS:
                return this.token.equals("-");
            case PLUS:
                return this.token.equals("+") || this.token.equals("-");
            case DOT:
                return this.token.equals("*");
            case SLASH:
                return this.token.equals("/");
            case CARET:
                return this.token.equals("^");
            case POW_SYM:
                return this.token.equals("pow");
            case NAT_SYM:
                return this.token.equals("nat");
            case MAX_SYM:
                return this.token.equals("max") || this.token.equals("min");
            case LOG_SYM:
                return this.token.equals("log");
            case KOMA:
                return this.token.equals(",");
            case LBRACKET:
                return this.token.equals("(");
            case RBRACKET:
                return this.token.equals(")");
            case LISTLBRACKET:
                return this.token.equals("[");
            case LISTRBRACKET:
                return this.token.equals("]");
            case LITERAL:
                return isNumber() || isVariable();
            default:
                return false;
        }
    }

    /**
     * Match the current token and discard.
     */
    private void consume(Symbol symbol) {
        if (!match(symbol)) {
            throw new ParserException();
        }

        this.token = getToken();
    }

    /**
     * Determine the length of the next token.
     */
    private int getTokenLength() {
        int length = 1;

        int c = this.input.charAt(this.index);

        if (Character.isDigit(c)) {
            while (this.index + length < this.input.length()) {
                if (Character.isDigit(this.input.charAt(this.index + length))) {
                    length ++;
                } else {
                    break;
                }
            }
        } else if (Character.isLetter(c)) {
            while (this.index + length < this.input.length()) {
                char d = this.input.charAt(this.index + length);
                if (Character.isLetter(d) || Character.isDigit(d) || d == '_' || d == '\'') {
                    length ++;
                } else {
                    break;
                }
            }
        }

        return length;
    }

    private void skipWhitespace() {
        while (this.index < this.input.length()) {
            if (Character.isWhitespace(this.input.charAt(this.index))) {
                this.index ++;
            } else {
                break;
            }
        }
    }

    /**
     * Read next token.
     */
    private String getToken() {
        skipWhitespace();

        if (this.index >= this.input.length()) {
            return null;
        }

        int length = getTokenLength();

        String res = this.input.substring(this.index, this.index+length);
        this.index += length;

        return res;
    }

    /**
     * Push the given grammar symbols on the stack in reversed order.
     */
    private void produce(Symbol ... symbols) {
        for (int i = symbols.length-1; i >= 0; i--) {
            this.symbolStack.push(symbols[i]);
        }
    }

    /**
     * Push the given grammar symbols on the stack if
     * the first one matches the token.
     */
    private void produceOnMatch(Symbol ... symbols) {
        assert symbols.length > 0;

        if (match(symbols[0])) {
            produce(symbols);
        }
    }

    /**
     * Parse the input string into a syntax tree.
     */
    private SyntaxTree createTree() {
        produce(SUM);

        while (!this.symbolStack.isEmpty()) {
            Symbol symbol = this.symbolStack.pop();


            switch (symbol) {
                case SUM:
                    produce(PROD, SUM_CONT);
                    break;
                case SUM_CONT:
                    produceOnMatch(PLUS, PROD, SUM_MARKER, SUM_CONT);
                    break;
                case PROD:
                    produce(POW, PROD_CONT);
                    break;
                case PROD_CONT:
                    produceOnMatch(DOT, POW, PROD_MARKER, PROD_CONT);
                    produceOnMatch(SLASH, POW, DIV_MARKER, PROD_CONT);
                    break;
                case POW:
                    if (match(POW_SYM)) {
                        produce(POW_SYM, LBRACKET, SUM, KOMA, SUM, RBRACKET, POW_MARKER);
                    } else {
                        produce(EXPR, POW_CONT);
                    }
                    break;
                case POW_CONT:
                    produceOnMatch(CARET, EXPR, POW_MARKER);
                    break;
                case LIST:
                    produce(SUM, LIST_CONT);
                    break;
                case LIST_CONT:
                    produceOnMatch(KOMA, SUM, LIST_MARKER, LIST_CONT);
                    break;
                case EXPR:
                    if (match(LBRACKET)) {
                        produce(LBRACKET, SUM, RBRACKET);
                    } else if (match(UNARY_MINUS)) {
                        produce(UNARY_MINUS, EXPR);
                    } else if (match(NAT_SYM)) {
                        produce(NAT_SYM, LBRACKET, SUM, RBRACKET, NAT_MARKER);
                    } else if (match(MAX_SYM)) {
                        produce(MAX_SYM, LBRACKET, LISTLBRACKET, LIST, LISTRBRACKET, RBRACKET, MAX_MARKER);
                    } else if (match(LOG_SYM)) {
                        produce(LOG_SYM, LBRACKET, SUM, KOMA, SUM, RBRACKET, LOG_MARKER);
                    } else {
                        produce(LITERAL);
                    }
                    break;
                case NAT_MARKER:
                    if (this.syntaxStack.size() < 1) {
                        throw new ParserException();
                    }
                    //do nothing, just ignore the nat()
                    break;
                case MAX_MARKER:
                    if (this.syntaxStack.size() < 1) {
                        throw new ParserException();
                    }
                    //do nothing, just ignore the max([]), already handled by LIST
                    break;
                case LOG_MARKER:
                    {
                        if (this.syntaxStack.size() < 2) {
                            throw new ParserException();
                        }
                        SyntaxTree right = this.syntaxStack.pop();
                        SyntaxTree left = this.syntaxStack.pop();
                        this.syntaxStack.push(new Op(LOG_MARKER, left, right));
                    }
                    break;
                case SUM_MARKER:
                case PROD_MARKER:
                case POW_MARKER:
                case DIV_MARKER:
                    {
                        if (this.syntaxStack.size() < 2) {
                            throw new ParserException();
                        }
                        SyntaxTree right = this.syntaxStack.pop();
                        SyntaxTree left = this.syntaxStack.pop();
                        this.syntaxStack.push(new Op(symbol, left, right));
                    }
                    break;
                case LIST_MARKER:
                    {
                        if (this.syntaxStack.size() < 2) {
                            throw new ParserException();
                        }
                        SyntaxTree right = this.syntaxStack.pop();
                        SyntaxTree left = this.syntaxStack.pop();
                        //list is only used for max at the moment
                        this.syntaxStack.push(new Op(MAX_MARKER, left, right));
                    }
                    break;
                default:
                    if (symbol != PLUS && symbol != UNARY_MINUS && match(UNARY_MINUS)) {
                        consume(UNARY_MINUS);
                    }

                    if (token == null) {
                        throw new ParserException();
                    }

                    if (isNumber()) {
                        this.syntaxStack.push(new Number(this.token));
                    } else if (isVariable()) {
                        this.syntaxStack.push(new TRSVariable(this.token));
                    }

                    consume(symbol);
                    break;
            }
        }

        if (this.syntaxStack.size() != 1) {
            throw new ParserException();
        }

        if (this.getToken() != null) {
            throw new ParserException();
        }

        return this.syntaxStack.pop();
    }

    private static boolean isConstant(SyntaxTree tree) {
        return tree instanceof Number;
    }

    private static boolean isMonomial(SyntaxTree tree) {
        if (!(tree instanceof Op)) {
            return false;
        }
        Op op = (Op)tree;
        if (op.operation == POW_MARKER && op.left instanceof TRSVariable && op.right instanceof Number) {
            Number r = (Number) op.right;
            assert r.compareTo(Number.ONE) >= 0;
            return true;
        }
        return false;
    }

    private static SyntaxTree collapseSum(SyntaxTree left, SyntaxTree right) {
        boolean constantLeft = isConstant(left);
        boolean constantRight = isConstant(right);

        if (constantLeft && constantRight) {
            Number numLeft = (Number)left;
            Number numRight = (Number)right;

            return new Number(numLeft.value.add(numRight.value));
        }

        if (constantLeft && !constantRight) {
            return right;
        }

        if (!constantLeft && constantRight) {
            return left;
        }

        boolean monomialLeft = isMonomial(left);
        boolean monomialRight = isMonomial(right);

        if (monomialLeft && monomialRight) {
            Op opLeft = (Op)left;
            Op opRight = (Op)right;

            Number numLeft = (Number)opLeft.right;
            Number numRight = (Number)opRight.right;

            if (numLeft.value.compareTo(numRight.value) > 0) {
                return left;
            } else {
                return right;
            }
        }

        if (!monomialLeft) {
            return left;
        } else {
            return right;
        }
    }

    private static SyntaxTree collapseProd(SyntaxTree left, SyntaxTree right) {

        if (isConstant(left)) {
            return right;
        }

        if (isConstant(right)) {
            return left;
        }

        if (isExp(left)) {
            BigInteger leftBase = getBase(left);
            if (isExp(right)) {
                BigInteger rightBase = getBase(right);
                return buildExp(leftBase.max(rightBase));
            } else {
                return buildExp(leftBase);
            }
        } else if (isExp(right)) {
            return buildExp(getBase(right));
        }

        boolean monomialLeft = isMonomial(left);
        boolean monomialRight = isMonomial(right);

        if (monomialLeft && !monomialRight) {
            return right;
        }

        if (!monomialLeft && monomialRight) {
            return left;
        }

        Op opLeft = (Op)left;
        Op opRight = (Op)right;

        Number numLeft = (Number)opLeft.right;
        Number numRight = (Number)opRight.right;

        return new Op(POW_MARKER, new TRSVariable("n"), new Number(numLeft.value.add(numRight.value)));
    }

    private static SyntaxTree buildExp(BigInteger i) {
        return new Op(POW_MARKER, new Number(i), new Op(POW_MARKER, new TRSVariable("n"), Number.ONE));
    }

    private static BigInteger getBase(SyntaxTree tree) {
        Op op = (Op) tree;
        BigInteger base = ((Number) op.left).value;
        Op exponent = (Op) op.right;
        BigInteger degree = ((Number) exponent.right).value;
        return base.multiply(degree);
    }

    private static boolean isExp(SyntaxTree tree) {
        if (tree instanceof Op) {
            Op op = (Op) tree;
            if (op.operation == POW_MARKER) {
                SyntaxTree base = op.left;
                if (base instanceof Number) {
                    assert ((Number) base).value.compareTo(BigInteger.ONE) > 0;
                    SyntaxTree exponent = op.right;
                    if (isMonomial(exponent)) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    private static SyntaxTree collapsePow(SyntaxTree left, SyntaxTree right) {
        boolean constantLeft = isConstant(left);
        boolean constantRight = isConstant(right);

        if (constantLeft && constantRight) {
            Number numLeft = (Number)left;
            Number numRight = (Number)right;

            return new Number(numLeft.value.pow(numRight.value.intValue()));
        }

        boolean monomialLeft = isMonomial(left);

        if (monomialLeft && constantRight) {
            Op opLeft = (Op)left;

            Number numLeft = (Number)opLeft.right;
            Number numRight = (Number)right;

            return new Op(POW_MARKER, new TRSVariable("n"), new Number(numLeft.value.multiply(numRight.value)));
        }

        return new Op(POW_MARKER, left, right);
    }

    private static SyntaxTree collapse(SyntaxTree tree) {
        if (tree instanceof Number) {
            return tree;
        } else if (tree instanceof TRSVariable) {
            return new Op(POW_MARKER, new TRSVariable("n"), Number.ONE);
        } else if (tree instanceof Op) {
            Op op = (Op)tree;

            SyntaxTree left = collapse(op.left);
            SyntaxTree right = collapse(op.right);

            switch (op.operation) {
                case SUM_MARKER:
                case MAX_MARKER:
                    return collapseSum(left, right);
                case PROD_MARKER:
                    return collapseProd(left, right);
                case POW_MARKER:
                    return collapsePow(left, right);
                case DIV_MARKER:
                    //replace A/B by A if B >= 1 (over-approximation)
                    if (right instanceof Number && ((Number)right).value.signum() >= 1) {
                        return left;
                    } else {
                        throw new RuntimeException();
                    }
                case LOG_MARKER:
                    //replace log(A,B) by B if A >= 1 (over-approximation)
                    if (left instanceof Number && ((Number)left).value.signum() >= 1) {
                        return right;
                    } else {
                        throw new RuntimeException();
                    }
                default:
                    throw new RuntimeException();
            }
        }

        return null;
    }

    /**
     * Over-approximate the maximum of two polynomials, under the assumption that
     * all coefficients are natural numbers and variables only range over natural
     * numbers. Then one can simply take the maximal coefficient for every term
     * that appears in at least one of the polynomials.
     */
    private static SimplePolynomial approximateMax(SimplePolynomial a, SimplePolynomial b) {
        SimplePolynomial res = SimplePolynomial.ZERO;
        Set<IndefinitePart> terms = new LinkedHashSet<>();
        terms.addAll(a.getSimpleMonomials().keySet());
        terms.addAll(b.getSimpleMonomials().keySet());

        for (IndefinitePart x : terms) {
            //FIXME: use getOrDefault as soon as ImmutableMap is fixed
            BigInteger coeffA = a.getSimpleMonomials().get(x);
            if (coeffA == null) coeffA = BigInteger.ZERO;

            BigInteger coeffB = b.getSimpleMonomials().get(x);
            if (coeffB == null) coeffB = BigInteger.ZERO;

            BigInteger coeff = coeffA.max(coeffB);
            res = res.plus(SimplePolynomial.create(x, coeff));
        }
        return res;
    }

    private static SimplePolynomial toPolynomial(SyntaxTree tree) throws NotRepresentableAsPolynomialException {
        if (tree instanceof Number) {
            return SimplePolynomial.create(((Number)tree).value);
        } else if (tree instanceof TRSVariable) {
            return SimplePolynomial.create(((TRSVariable)tree).name);
        } else if (tree instanceof Op) {
            Op op = (Op)tree;

            SimplePolynomial lhs = toPolynomial(op.left);
            SimplePolynomial rhs = toPolynomial(op.right);

            switch (op.operation) {
            case SUM_MARKER:
                return lhs.plus(rhs);
            case MAX_MARKER:
                return approximateMax(lhs, rhs);
            case PROD_MARKER:
                return lhs.times(rhs);
            case POW_MARKER:
                if (!rhs.isConstant()) {
                    throw new NotRepresentableAsPolynomialException();
                }
                int n;
                try {
                    n = rhs.getConstantSize().intValueExact();
                } catch (ArithmeticException e) {
                    throw new NotRepresentableAsPolynomialException();
                }
                return lhs.power(n);
            case DIV_MARKER:
                //replace A/B by A if B >= 1 (over-approximation)
                if (rhs.isConstant() && rhs.allPositive()) {
                    return lhs;
                } else {
                    throw new NotRepresentableAsPolynomialException();
                }
            case LOG_MARKER:
                //replace log(A,B) by B if A >= 1
                if (lhs.isConstant() && lhs.allPositive()) {
                    return rhs;
                } else {
                    throw new NotRepresentableAsPolynomialException();
                }
            default:
                throw new RuntimeException();
            }
        }
        return null;
    }

    private static ComplexityValue toComplexityValue(SyntaxTree tree) {
        if (isConstant(tree)) {
            return ComplexityValue.constant();
        }
        if (isMonomial(tree)) {
            Op op = (Op)tree;
            Number num = (Number) op.right;
            return ComplexityValue.fixedDegreePoly((num.value.intValue()));
        }
        if (isExp(tree)) {
            return ComplexityValue.exponential();
        }
        throw new RuntimeException("unable to derive a complexity value from PUBS' answer");
    }

    /**
     * Input is of the form YES(?, poly).
     */
    public static ComplexityValue parse(String input) {
        SyntaxTree tree;
        try {
            PUBSParser parser = new PUBSParser(input);
            tree = parser.createTree();
        } catch (ParserException e) {
            System.err.println("WARNING: Error while parsing: " + input);
            return ComplexityValue.infinite();
        }
        SyntaxTree collapsedTree = collapse(tree);
        return toComplexityValue(collapsedTree);
    }

    /**
     * Input is of the form YES(?, poly).
     * @throws NotRepresentableAsPolynomialException 
     */
    public static SimplePolynomial parseAsPolynomial(String input) throws NotRepresentableAsPolynomialException {
        SyntaxTree tree;
        try {
            PUBSParser parser = new PUBSParser(input);
            tree = parser.createTree();
        } catch (ParserException e) {
            System.err.println("WARNING: Error while parsing: " + input);
            throw new NotRepresentableAsPolynomialException();
        }
        return toPolynomial(tree);
    }
}
