package aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp;

import java.io.*;

class SExpTokenizer {

    static class Token {
        final String lexeme;
        final TokenType tokenType;

        Token(TokenType tokenType, String lexeme) {
            this.tokenType = tokenType;
            this.lexeme = lexeme;
        }

        @Override
        public String toString() {
            return this.tokenType + ": " + this.lexeme;
        }
    }

    static enum TokenType {
        Binary, Close, Decimal, Hexadecimal, Keyword, Numeral, Open, String, Symbol
    }

    static boolean isDigit(char c) {
        return '0' <= c && c <= '9';
    }

    private static boolean isHexDigit(char c) {
        return SExpTokenizer.isDigit(c) || 'a' <= c && c <= 'f' || 'A' <= c && c <= 'F';
    }

    static boolean isKeywordChar(char c) {
        switch (c) {
        case '~':
        case '!':
        case '@':
        case '$':
        case '%':
        case '^':
        case '&':
        case '*':
        case '_':
        case '-':
        case '+':
        case '=':
        case '<':
        case '>':
        case '.':
        case '?':
        case '/':
        case ':':
            return true;
        }
        return SExpTokenizer.isLetterOrDigit(c);
    }

    private static boolean isLetter(char c) {
        return 'a' <= c && c <= 'z' || 'A' <= c && c <= 'Z';
    }

    private static boolean isLetterOrDigit(char c) {
        return SExpTokenizer.isLetter(c) || SExpTokenizer.isDigit(c);
    }

    private int c = -1;

    private Reader r;

    SExpTokenizer(Reader r) throws IOException {
        this.r = r;
    }

    private char next() throws IOException, ParserException {
        int c = this.c != -1 ? this.c : this.r.read();
        if (c == -1) {
            throw new ParserException("end of file");
        }
        this.c = -1;
        return (char) c;
    }

    private char nextAfterSpaces() throws IOException, ParserException {
        while (true) {
            char c = this.next();
            switch (c) {
            case ';':
                do {
                    c = this.next();
                } while (c != '\n' && c != '\r');
                break;
            case ' ':
            case '\t':
            case '\n':
            case '\r':
                break;
            default:
                return c;
            }
        }
    }

    private void pushback(char c) {
        this.c = c;
    }

    Token token() throws IOException, ParserException {
        char c = this.nextAfterSpaces();
        StringBuilder lexeme = new StringBuilder();
        lexeme.append(c);
        switch (c) {
        case '(':
            return new Token(TokenType.Open, "(");
        case ')':
            return new Token(TokenType.Close, ")");
        case '0': // Numeral
            return new Token(TokenType.Numeral, "0");
        case '1':
        case '2':
        case '3':
        case '4':
        case '5':
        case '6':
        case '7':
        case '8':
        case '9':
            // Numeral or decimal
            c = this.next();
            while (SExpTokenizer.isDigit(c)) {
                lexeme.append(c);
                c = this.next();
            }
            if (c == '.') {
                lexeme.append(c);
                c = this.next();
                while (SExpTokenizer.isDigit(c)) {
                    lexeme.append(c);
                    this.next();
                }
                this.pushback(c);
                return new Token(TokenType.Decimal, lexeme.toString());
            } else {
                this.pushback(c);
                return new Token(TokenType.Numeral, lexeme.toString());
            }
        case '#':
            c = this.next();
            if (c == 'x') {
                do {
                    lexeme.append(c);
                    c = this.next();
                } while (SExpTokenizer.isHexDigit(c));
                this.pushback(c);
                return new Token(TokenType.Hexadecimal, lexeme.toString());
            } else if (c == 'b') {
                do {
                    lexeme.append(c);
                    c = this.next();
                } while (c == '0' || c == '1');
                this.pushback(c);
                return new Token(TokenType.Binary, lexeme.toString());
            } else {
                throw new ParserException("Invalid char after #: '" + Character.toString(c) + "'\n");
            }
        case '"':
            c = this.next();
            do {
                lexeme.append(c);
                if (c == '\\') {
                    c = this.next();
                    lexeme.append(c);
                    if (c != '\\' && c != '"') {
                        throw new ParserException("Invalid escpae sequence \"\\" + Character.toString(c) + "\"");
                    }
                    continue;
                }
                c = this.next();
            } while (c != '"');
            lexeme.append(c);
            return new Token(TokenType.String, lexeme.toString());
        case ':':
            c = this.next();
            while (SExpTokenizer.isKeywordChar(c)) {
                lexeme.append(c);
                c = this.next();
            }
            this.pushback(c);
            return new Token(TokenType.Keyword, lexeme.toString());
        }
        if (SExpTokenizer.isKeywordChar(c)) {
            c = this.next();
            while (SExpTokenizer.isKeywordChar(c)) {
                lexeme.append(c);
                c = this.next();
            }
            this.pushback(c);
            return new Token(TokenType.Symbol, lexeme.toString());
        }
        throw new ParserException("unexpected char: " + Character.toString(c));
    }
}
