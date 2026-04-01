package aprove.input.Programs.fp;

import java.io.*;
import java.util.*;

import aprove.input.Generated.fp.lexer.*;
import aprove.input.Generated.fp.node.*;

public class FPLexer extends Lexer {

    protected Set tokens;

    public FPLexer(PushbackReader r, Set s) {
    super(r);
    this.tokens = s;
    }

    @Override
    protected Token getToken() throws IOException, LexerException {
    Token t = super.getToken();
    String name = t.toString().trim();
    if ((t instanceof TId) && (!this.tokens.contains(name))) {
        TNoappid ft = new TNoappid(t.getText(), t.getLine(), t.getPos());
        return ft;
    }
    return t;
    }

}
