package aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp;

import java.io.*;
import java.math.*;
import java.util.*;

import immutables.*;

public class SExpStreamParser {

    private final SExpTokenizer toks;

    public SExpStreamParser(Reader r) throws IOException {
        this.toks = new SExpTokenizer(r);
    }

    public SExp parse() throws ParserException, IOException {
        ArrayList<SExp> top = new ArrayList<>();
        ArrayDeque<ArrayList<SExp>> stack = new ArrayDeque<>();

        while (!stack.isEmpty() || top.size() != 1) {
            SExpTokenizer.Token t = this.toks.token();
            switch (t.tokenType) {
            case Open:
                stack.add(top);
                top = new ArrayList<>();
                break;
            case Close:
                if (stack.size() < 1) {
                    throw new ParserException("unexpected ')'");
                }
                SExpList l = new SExpList(ImmutableCreator.create(top));
                top = stack.removeLast();
                top.add(l);
                break;
            case Symbol:
                top.add(new SExpSymbol(t.lexeme));
                break;
            case Binary:
                top.add(new SExpBinary(new BigInteger(t.lexeme.substring(2), 2)));
                break;
            case Hexadecimal:
                top.add(new SExpHexadecimal(new BigInteger(t.lexeme.substring(2), 16)));
                break;
            case Decimal:
                top.add(new SExpDecimal(new BigDecimal(t.lexeme)));
                break;
            case Keyword:
                top.add(SExpKeyword.get(t.lexeme));
                break;
            case Numeral:
                top.add(new SExpNumeral(new BigInteger(t.lexeme)));
                break;
            case String:
                top.add(new SExpString(this.unquote(t.lexeme)));
                break;
            default:
                throw new ParserException("Unexpected token: " + t);
            }
        }

        if (!stack.isEmpty() || top.size() != 1) {
            throw new ParserException("Unexpected end of file");
        }

        return top.get(0);
    }

    private String unquote(String s) {
        int l = s.length();
        assert l >= 2;
        assert s.charAt(0) == '"';
        assert s.charAt(l - 1) == '"';
        StringBuilder sb = new StringBuilder();
        for (int i = 1; i < l - 1; ++i) {
            char c = s.charAt(i);
            if (c == '\\') {
                i++;
                assert i < l - 1;
                c = s.charAt(i);
            }
            sb.append(c);
        }
        return sb.toString();
    }
}
