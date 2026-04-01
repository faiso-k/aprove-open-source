package aprove.input.Programs.haskell;

import java.io.*;
import java.util.*;

import aprove.input.Generated.haskell.lexer.*;
import aprove.input.Generated.haskell.node.*;
import aprove.input.Generated.haskell.parser.*;

public class HaskellParser extends aprove.input.Generated.haskell.parser.Parser{
    LayoutLexer laylex;
    boolean non;

    public HaskellParser(LayoutLexer lexer){
        super(lexer);
        this.laylex = lexer;
        this.non = false;
    }

    @Override
    public Start parse() throws ParserException, LexerException, IOException {
         while (true){
            try {
                return super.parse();
            } catch (ParserException pe) {
                Token t = this.laylex.peek();
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    System.err.println(pe.getMessage());
                    System.err.println(t.getText()+" --- "+t.getLine()+","+t.getPos()+" -- "+t.getClass().getName());
                }
                if (this.laylex.peek() instanceof TWclose) {
                    throw pe;
                }
                this.non = true;
                if (!this.laylex.insertMissing()) {
                    throw pe;
                }
            }
         }
    }

    @Override
    public void push(int numstate, ArrayList listNode) throws ParserException, LexerException, IOException {
        if (this.non) { this.non= false; return; }
        super.push(numstate,listNode);
    }

}
