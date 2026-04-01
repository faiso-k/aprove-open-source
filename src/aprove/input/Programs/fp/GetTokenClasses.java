package aprove.input.Programs.fp;

import java.io.*;
import java.util.*;

import aprove.input.Generated.fppp.lexer.*;
import aprove.input.Generated.fppp.node.*;
import aprove.input.Generated.fppp.parser.*;
import aprove.input.Utility.*;

public class GetTokenClasses {

    public static void getTokens(Reader reader, Set tokens, ParseErrors errors) {
    Start tree = null;
    try {
        tree = new Parser(new Lexer(new PushbackReader(reader, 1024))).parse();
        GetTokenClassesPass p = new GetTokenClassesPass();
        p.setTokens(tokens);
        p.setErrors(errors);
        tree.apply(p);
    }
    catch (Exception e) {
        ParseError pe = new ParseError(ParseError.ERROR);
        if (e instanceof ParserException) {
        Token t = ((ParserException)e).getToken();
        pe.setToken(t.toString().trim());
        pe.setPosition(t.getLine(), t.getPos());
        }
        pe.setMessage(e.getMessage());
        errors.add(pe);
    }
    }

}
