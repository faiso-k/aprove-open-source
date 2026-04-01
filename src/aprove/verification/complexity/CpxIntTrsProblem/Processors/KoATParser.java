package aprove.verification.complexity.CpxIntTrsProblem.Processors;

import static aprove.verification.complexity.CpxIntTrsProblem.Processors.KoATParser.Symbol.*;

import java.math.*;
import java.util.*;

import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * Parse KoAT complexity value, based on the following LL(1) grammar:
 *
 * SUM       -> PROD SUM_CONT
 * SUM_CONT  -> + PROD SUM_MARKER SUM_CONT | - PROD SUBTRACTION_MARKER SUM_CONT | eps
 * PROD      -> POW PROD_CONT
 * PROD_CONT -> * POW PROD_MARKER PROD_CONT | eps
 * POW       -> EXPR POW_CONT | pow ( SUM , SUM ) POW_MARKER
 * POW_CONT  -> ^ EXPR POW_MARKER | eps
 * EXPR      -> ( SUM ) | lit | nat ( lit ) NAT_MARKER | - lit UNARY_MINUS_MARKER
 *
 * @author Felix Bier
 *
 */
public class KoATParser {

    @SuppressWarnings("serial")
    private static class ParserException extends RuntimeException {}

    public enum Symbol {
        SUM, SUM_CONT, PLUS, SUM_MARKER, MINUS, SUBTRACTION_MARKER,
        PROD, PROD_CONT, DOT, PROD_MARKER,
        POW, POW_CONT, CARET, POW_SYM, KOMA, POW_MARKER,
        EXPR, LBRACKET, RBRACKET, LITERAL, NAT_SYM, NAT_MARKER, UNARY_MINUS, UNARY_MINUS_MARKER
    }

    private static List<String> reserved = new LinkedList<>
        (Arrays.asList(new String[]{"nat", "pow"}));

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

    private static class Variable extends SyntaxTree {
        String name;

        public Variable(String token) {
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
            String opString;
            switch (operation) {
                case SUM_MARKER:
                    opString = " + ";
                    break;
                case SUBTRACTION_MARKER:
                    opString = " - ";
                    break;
                case PROD_MARKER:
                    opString = " * ";
                    break;
                case POW_MARKER:
                    opString = " ^ ";
                    break;
                default:
                    throw new RuntimeException();
            }
            return "(" + left + opString + right + ")";
        }
    }

    private static class UnaryOp extends SyntaxTree {
        SyntaxTree tree;
        Symbol operation;

        public UnaryOp(Symbol operation, SyntaxTree tree) {
            this.operation = operation;
            this.tree = tree;
        }

        @Override
        public String toString() {
            String opString;
            switch (operation) {
                case UNARY_MINUS_MARKER:
                    opString = "-";
                    break;
                default:
                    throw new RuntimeException();
            }
            return "(" + opString + tree + ")";
        }
    }

    private String input;
    private String token;

    private int index;

    private LinkedList<Symbol> symbolStack;
    private LinkedList<SyntaxTree> syntaxStack;

    private KoATParser(String input) {
        this.input = input;
        this.token = this.getToken();

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
        return Character.isLetter(this.token.charAt(0)) && !KoATParser.reserved.contains(this.token);
    }

    /**
     * Check if the current token matches the given grammar symbol.
     */
    private boolean match(Symbol sym) {

        if (this.token == null) {
            return false;
        }

        switch (sym) {
            case UNARY_MINUS: case MINUS:
                return this.token.equals("-");
            case PLUS:
                return this.token.equals("+");
            case DOT:
                return this.token.equals("*");
            case CARET:
                return this.token.equals("^");
            case POW_SYM:
                return this.token.equals("pow");
            case NAT_SYM:
                return this.token.equals("nat");
            case KOMA:
                return this.token.equals(",");
            case LBRACKET:
                return this.token.equals("(");
            case RBRACKET:
                return this.token.equals(")");
            case LITERAL:
                return this.isNumber() || this.isVariable();
            default:
                return false;
        }
    }

    /**
     * Match the current token and discard.
     */
    private void consume(Symbol symbol) {
        if (!this.match(symbol)) {
            throw new ParserException();
        }

        this.token = this.getToken();
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
        this.skipWhitespace();

        if (this.index >= this.input.length()) {
            return null;
        }

        int length = this.getTokenLength();

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

        if (this.match(symbols[0])) {
            this.produce(symbols);
        }
    }

    /**
     * Parse the input string into a syntax tree.
     */
    private SyntaxTree createTree() {
        this.produce(SUM);

        while (!this.symbolStack.isEmpty()) {
            Symbol symbol = this.symbolStack.pop();


            switch (symbol) {
                case SUM:
                    this.produce(PROD, SUM_CONT);
                    break;
                case SUM_CONT:
                    this.produceOnMatch(PLUS, PROD, SUM_MARKER, SUM_CONT);
                    this.produceOnMatch(MINUS, PROD, SUBTRACTION_MARKER, SUM_CONT);
                    break;
                case PROD:
                    this.produce(POW, PROD_CONT);
                    break;
                case PROD_CONT:
                    this.produceOnMatch(DOT, POW, PROD_MARKER, PROD_CONT);
                    break;
                case POW:
                    if (this.match(POW_SYM)) {
                        this.produce(POW_SYM, LBRACKET, SUM, KOMA, SUM, RBRACKET, POW_MARKER);
                    } else {
                        this.produce(EXPR, POW_CONT);
                    }
                    break;
                case POW_CONT:
                    this.produceOnMatch(CARET, EXPR, POW_MARKER);
                    break;
                case EXPR:
                    if (match(LBRACKET)) {
                        this.produce(LBRACKET, SUM, RBRACKET);
                    } else if (match(NAT_SYM)) {
                        this.produce(NAT_SYM, LBRACKET, LITERAL, RBRACKET);
                    } else if (match(UNARY_MINUS)) {
                        this.produce(UNARY_MINUS, LITERAL, UNARY_MINUS_MARKER);
                    } else {
                        this.produce(LITERAL);
                    }
                    break;
                case NAT_MARKER:
                    if (this.syntaxStack.size() < 1) {
                        throw new ParserException();
                    }

                    // var is on top of syntax stack, leave it there
                    break;
                case SUM_MARKER:
                case SUBTRACTION_MARKER:
                case PROD_MARKER:
                case POW_MARKER:
                    if (this.syntaxStack.size() < 2) {
                        throw new ParserException();
                    }

                    SyntaxTree right = this.syntaxStack.pop();
                    SyntaxTree left = this.syntaxStack.pop();

                    this.syntaxStack.push(new Op(symbol, left, right));
                    break;
                case UNARY_MINUS_MARKER:
                    if (this.syntaxStack.size() < 1) {
                        throw new ParserException();
                    }
                    SyntaxTree tree = this.syntaxStack.pop();
                    this.syntaxStack.push(new UnaryOp(symbol, tree));
                    break;
                default:
                    if (this.isNumber()) {
                        this.syntaxStack.push(new Number(this.token));
                    } else if (this.isVariable()) {
                        this.syntaxStack.push(new Variable(this.token));
                    }

                    this.consume(symbol);
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
        if (op.operation == POW_MARKER && op.left instanceof Variable && op.right instanceof Number) {
            Number r = (Number) op.right;
            assert r.compareTo(Number.ONE) >= 0;
            return true;
        }
        return false;
    }

    private static SyntaxTree negate(SyntaxTree tree) {
        if (tree instanceof Number)
            return new Number(((Number) tree).value.negate());
        else
            return new Op(PROD_MARKER, new Number(BigInteger.valueOf(-1)), tree);
    }

    private static SyntaxTree collapseSum(SyntaxTree left, SyntaxTree right) {
        boolean constantLeft = KoATParser.isConstant(left);
        boolean constantRight = KoATParser.isConstant(right);

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

        boolean monomialLeft = KoATParser.isMonomial(left);
        boolean monomialRight = KoATParser.isMonomial(right);

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

        if (KoATParser.isConstant(left)) {
            return right;
        }

        if (KoATParser.isConstant(right)) {
            return left;
        }

        if (KoATParser.isExp(left)) {
            BigInteger leftBase = KoATParser.getBase(left);
            if (KoATParser.isExp(right)) {
                BigInteger rightBase = KoATParser.getBase(right);
                return KoATParser.buildExp(leftBase.max(rightBase));
            } else {
                return KoATParser.buildExp(leftBase);
            }
        } else if (KoATParser.isExp(right)) {
            return KoATParser.buildExp(getBase(right));
        }

        boolean monomialLeft = KoATParser.isMonomial(left);
        boolean monomialRight = KoATParser.isMonomial(right);

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

        return new Op(POW_MARKER, new Variable("n"), new Number(numLeft.value.add(numRight.value)));
    }

    private static SyntaxTree buildExp(BigInteger i) {
        return new Op(POW_MARKER, new Number(i), new Op(POW_MARKER, new Variable("n"), Number.ONE));
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
        boolean constantLeft = KoATParser.isConstant(left);
        boolean constantRight = KoATParser.isConstant(right);

        if (constantLeft && constantRight) {
            Number numLeft = (Number)left;
            Number numRight = (Number)right;

            return new Number(numLeft.value.pow(numRight.value.intValue()));
        }

        boolean monomialLeft = KoATParser.isMonomial(left);

        if (monomialLeft && constantRight) {
            Op opLeft = (Op)left;

            Number numLeft = (Number)opLeft.right;
            Number numRight = (Number)right;

            return new Op(POW_MARKER, new Variable("n"), new Number(numLeft.value.multiply(numRight.value)));
        }

        return new Op(POW_MARKER, left, right);
    }

    private static SyntaxTree collapse(SyntaxTree tree) {
        if (tree instanceof Number) {
            return tree;
        } else if (tree instanceof Variable) {
            return new Op(POW_MARKER, new Variable("n"), Number.ONE);
        } else if (tree instanceof Op) {
            Op op = (Op)tree;

            SyntaxTree left = KoATParser.collapse(op.left);
            SyntaxTree right = KoATParser.collapse(op.right);

            switch (op.operation) {
                case SUM_MARKER:
                    return KoATParser.collapseSum(left, right);
                case SUBTRACTION_MARKER:
                    return KoATParser.collapseSum(left, collapse(negate(right)));
                case PROD_MARKER:
                    return KoATParser.collapseProd(left, right);
                case POW_MARKER:
                    return KoATParser.collapsePow(left, right);
                default:
                    throw new RuntimeException();
            }
        } else if (tree instanceof UnaryOp) {
            UnaryOp op = (UnaryOp)tree;
            SyntaxTree subTree = KoATParser.collapse(op.tree);

            switch (op.operation) {
            case UNARY_MINUS_MARKER:
                return KoATParser.collapse(negate(subTree));
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
        if (KoATParser.isMonomial(tree)) {
            Op op = (Op)tree;
            Number num = (Number) op.right;
            return ComplexityValue.fixedDegreePoly(num.value.intValue());
        }
        if (isExp(tree)) {
            return ComplexityValue.exponential();
        }
        throw new RuntimeException("unable to derive a complexity value from KoAT's answer");
    }

    /**
     * Input is of the form YES(?, poly).
     */
    public static ComplexityValue parse(String input) {
        if (input.equals("INF")) {
            return ComplexityValue.infinite();
        } else if (input.equals("EXP")) {
            return ComplexityValue.exponential();
        }
        KoATParser parser = new KoATParser(input);
        SyntaxTree tree = parser.createTree();
        SyntaxTree collapsedTree = collapse(tree);
        return toComplexityValue(collapsedTree);
    }

    private static SimplePolynomial collapsePoly(SyntaxTree tree) {
        if (tree instanceof Number) {
            return SimplePolynomial.create(((Number) tree).value);
        } else if (tree instanceof Variable) {
            return SimplePolynomial.create(((Variable) tree).name);
        } else if (tree instanceof Op) {
            Op op = (Op)tree;

            SimplePolynomial left = KoATParser.collapsePoly(op.left);
            SimplePolynomial right = KoATParser.collapsePoly(op.right);

            switch (op.operation) {
                case SUM_MARKER:
                    return left.plus(right);
                case SUBTRACTION_MARKER:
                    return left.minus(right);
                case PROD_MARKER:
                    return left.times(right);
                case POW_MARKER:
                    BigInteger r = right.getConstantSize();
                    if (r == null) {
                        throw new NonConstantExponentException(right);
                    }
                    return left.power(r.intValueExact());
                default:
                    throw new RuntimeException();
            }
        } else if (tree instanceof UnaryOp) {
            UnaryOp op = (UnaryOp)tree;
            SimplePolynomial subTree = KoATParser.collapsePoly(op.tree);

            switch (op.operation) {
            case UNARY_MINUS_MARKER:
                return subTree.negate();
            default:
                throw new RuntimeException();
            }

        } else {
            throw new RuntimeException("Unexpected Parser Error in tree: " + tree);
        }
    }

    public static class NonConstantExponentException extends RuntimeException {
        private static final long serialVersionUID = -5143790932590642978L;
        private SimplePolynomial exponent;

        public NonConstantExponentException(SimplePolynomial exponent) {
            super("tried to parse a Koat result with non constant exponent (" + exponent + ") as SimplePolynomial");
            this.exponent = exponent;
        }
        public SimplePolynomial getExponent() {
            return exponent;
        }
    }

    /**
     * Input is of the form YES(?, poly).
     */
    public static SimplePolynomial parseAsPolynomial(String input) {
        KoATParser parser = new KoATParser(input);
        SyntaxTree tree = parser.createTree();
        return collapsePoly(tree);
    }
}
