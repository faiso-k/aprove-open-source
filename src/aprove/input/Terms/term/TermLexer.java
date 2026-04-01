package aprove.input.Terms.term;

import java.io.*;
import java.util.*;

import aprove.input.Generated.term.lexer.*;
import aprove.input.Generated.term.node.*;

public class TermLexer extends Lexer {

    protected Set prefixIds;
    protected Set infixIds;

    public TermLexer(PushbackReader r, Set prefixIds, Set infixIds) {
    super(r);
    this.prefixIds = prefixIds;
    this.infixIds = infixIds;
    }

    /** This getToken-method reevaluates the tokenclass.
     */
    @Override
    protected Token getToken() throws IOException, LexerException {
    Token t = super.getToken();
    if ((t instanceof TPrefixId) || (t instanceof TInfixId) || (t instanceof TVarId)) {
        String name = t.toString().trim();
        Token ft;
        if (this.prefixIds.contains(name)) {
        ft = new TPrefixId(t.getText(), t.getLine(), t.getPos());
        }
        else if (this.infixIds.contains(name)) {
        ft = new TInfixId(t.getText(), t.getLine(), t.getPos());
        }
        else {
        ft = new TVarId(t.getText(), t.getLine(), t.getPos());
        }
        return ft;
    }
    return t;
    }

}
