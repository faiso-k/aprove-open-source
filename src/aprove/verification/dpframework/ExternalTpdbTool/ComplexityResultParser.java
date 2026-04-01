package aprove.verification.dpframework.ExternalTpdbTool;

import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Parses Strings like {@literal "YES (O(1), O(EXP) )"} to corresponding pairs of {@link ComplexityValue}s.
 *
 */
class ComplexityResultParser {

    /**
     * Thrown on parser errors. Encapsulates a message representing the expected value at a certain position.
     */
    static class ParserException extends Exception {
        /**
         * @param msg Describes the expected lexeme at the current position.
         */
        public ParserException(final String msg) {
            super(msg);
        }
    }

    /**
     * Parses Strings like {@literal "YES (O(1), O(EXP) )"} to corresponding pairs of {@link ComplexityValue}s.
     * @param in The {@link String} to parse.
     * @return the {@link Pair} of values, the first being the lower and the second being the upper bound.
     * @throws ParserException If an parse error occurred.
     */
    static Pair<ComplexityValue, ComplexityValue> parse(final String in) throws ComplexityResultParser.ParserException {
        return new ComplexityResultParser(in).parseLowerUpper();
    }

    /**
     * The input String.
     */
    private final char[] input;

    /**
     * The current position in the string. Will be decreased for backtracking.
     */
    private int pos;

    /**
     * Initializes the parser with the input {@code in}.
     * @param in The {@code String} to parse.
     */
    private ComplexityResultParser(final String in) {
        this.input = in.toCharArray();
        this.pos = 0;
    }

    /**
     * @return if the end of the input is reached.
     */
    private boolean eof() {
        return this.pos == this.input.length;
    }

    /**
     * Increases the position by one, if the current character in the input is {@code c}. Does nothing otherwise.
     * @param c The character to check for.
     * @return {@literal true} if the current character is {@code c}. {@literal false} otherwise.
     */
    private boolean expect(final char c) {
        if (this.input.length > this.pos && this.input[this.pos] == c) {
            ++this.pos;
            return true;
        }
        return false;
    }

    /**
     * Increases the position by {@code s.length} characters, if the {@link String} {@code s} occurs at the current
     * position in the input. Does nothing otherwise.
     * @param s The {@code String} to check for.
     * @return {@literal true} if {@code s} is at the current position of the input, {@literal false} otherwise.
     */
    private boolean expect(final String s) {
        final int p = this.pos;
        for (final char c : s.toCharArray()) {
            if (!this.expect(c)) {
                this.pos = p;
                return false;
            }
        }
        return true;
    }

    /**
     * Parses a complete complexity result and checks for end of input.
     * @return A {@link Pair} of {@link ComplexityValue}s, the first being the lower, the second being the upper bound.
     * @throws ParserException If a parse error occurred.
     */
    private Pair<ComplexityValue, ComplexityValue> parseLowerUpper() throws ComplexityResultParser.ParserException {
        this.require("YES");
        this.spaces();
        this.require("(");
        this.spaces();
        ComplexityValue lower = this.requireComplexityValue();
        if (lower == null) {
            lower = ComplexityValue.constant();
        }
        this.require(",");
        this.spaces();
        ComplexityValue upper = this.requireComplexityValue();
        if (upper == null) {
            upper = ComplexityValue.infinite();
        }
        this.require(")");
        this.spaces();
        if (!this.eof()) {
            throw new ComplexityResultParser.ParserException("eof");
        }
        return new Pair<>(lower, upper);
    }

    /**
     * Throws an exception if the current position in the input is not {@code s}, increases the current position by {@code s.length}, otherwise.
     * @param s The {@link String} to check for in the input.
     * @throws ParserException If {@code s} is not at the current position in the input.
     */
    private void require(final String s) throws ComplexityResultParser.ParserException {
        if (!this.expect(s)) {
            throw new ComplexityResultParser.ParserException(s);
        }
    }

    /**
     * Parses a {@link ComplexityValue} represented by Strings like {@literal "O(1)"}, {@literal "O(n^k)"} for some natural number {@code k}.
     * @return The {@link ComplexityValue} at the current position.
     * @throws ParserException If the current position is no {@literal "O(...)"} term.
     */
    private ComplexityValue requireBigO() throws ComplexityResultParser.ParserException {
        ComplexityValue rv = null;
        this.require("O");
        this.spaces();
        this.require("(");
        this.spaces();
        if (this.expect('1')) {
            rv = ComplexityValue.constant();
        } else {
            this.require("n");
            this.spaces();
            this.require("^");
            this.spaces();
            rv = ComplexityValue.fixedDegreePoly(this.requireNaturalNumber());
        }
        this.spaces();
        this.require(")");
        this.spaces();
        return rv;
    }

    /**
     * Parses values like {@literal "POLY"}, {@literal "EXP"}, {@literal "INF"}, and O-Notation.
     * @return The {@link ComplexityValue} represented by the input.
     * @throws ParserException If no {@linkOn parse errors ComplexityValue} could be parsed.
     */
    private ComplexityValue requireComplexityValue() throws ComplexityResultParser.ParserException {
        if (this.expect("?")) {
            this.spaces();
            return null;
        }
        if (this.expect("POLY")) {
            this.spaces();
            return ComplexityValue.polynomial();
        }
        if (this.expect("EXP")) {
            this.spaces();
            return ComplexityValue.exponential();
        }
        if (this.expect("INF")) {
            this.spaces();
            return ComplexityValue.infinite();
        }
        return this.requireBigO();
    }

    /**
     * Parses an natural number.
     * @return The parsed number.
     * @throws ParserException If there is no natural number at the current position.
     */
    private int requireNaturalNumber() throws ComplexityResultParser.ParserException {
        final StringBuilder sb = new StringBuilder();
        final int p = this.pos;
        while (this.pos < this.input.length && this.input[this.pos] >= '0' && this.input[this.pos] <= '9') {
            sb.append(this.input[this.pos]);
            ++this.pos;
        }
        try {
            return Integer.parseInt(sb.toString());
        } catch (final NumberFormatException e) {
            this.pos = p;
            throw new ComplexityResultParser.ParserException("natural number");
        }
    }

    /**
     * Eats up as much spaces in the input as possible (and increases {@code pos} accordingly).
     */
    private void spaces() {
        while (this.expect(' ')) {
            // expect already does all the work.
        }
    }
}
