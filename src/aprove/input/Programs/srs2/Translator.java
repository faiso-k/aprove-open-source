/**
 *
 * @author weidmann
 * @version $Id$
 */

package aprove.input.Programs.srs2;

/*
 * This class first executes the lexer, then the parser.
 * The parser builds the abstract syntax tree (AST).
 * SecondPass then traverses the AST and collects information,
 * which is then passed to the ObligationCreator.
 * The ObligationCreator tries to create proof obligations out of this information.
 */

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.input.Generated.srs2.lexer.*;
import aprove.input.Generated.srs2.node.*;
import aprove.input.Generated.srs2.parser.*;
import aprove.input.Utility.*;
import aprove.verification.oldframework.Input.*;


public class Translator extends aprove.verification.oldframework.Input.Translator.TranslatorSkeleton {
    Language language = null;

    private static Logger logger = Logger.getLogger("aprove.InputModels.Programs.srs2.Translator");

    @Override
    public Language getLanguage() {
        return this.language;
    }

    @Override
    public void translate(Reader reader) {
        this.setState(null);
        SecondPass sp = null;
        try {
            Lexer lexer = new Lexer(new PushbackReader(reader,1024));
            Parser parser = new Parser(lexer);
            Start tree = parser.parse();

            FirstPass fp = new  FirstPass();
            tree.apply(fp);
            sp = new SecondPass(fp.getFunctionSymbolNames());
            tree.apply(sp);

            if(Globals.DEBUG_WEIDMANN) {
                System.err.println("Normal Rules:\n" + sp.getNormalRules().toString());
                System.err.println("Relative Rules:\n" + sp.getRelativeRules().toString());
                System.err.println("Strategy leftmost: " + sp.getLeftmost());
                System.err.println("Strategy rightmost: " + sp.getRightmost());
            }

        }
        catch (Exception e) {
            ParseError pe = new ParseError(ParseError.ERROR);
            if (e instanceof ParserException) {
                Token t = ((ParserException) e).getToken();
                pe.setToken(t.toString().trim());
                pe.setPosition(t.getLine(), t.getPos());
                pe.setMessage("Error parsing input: " + e.getMessage());
            } else if (e instanceof LexerException) {
                pe.setMessage("Lexer exception: " + e.getMessage());
            } else {
                pe.setMessage("Unknown error: " + e.getMessage());
                if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
                    e.printStackTrace();
                }
            }
            this.getErrors().add(pe);
            // System.err.flush();
        }

        if(!this.getErrors().isEmpty()) // if there were errors so far
        {
            this.setState(null);
            this.language = Language.SRS; // was: QTRS

            if(Globals.DEBUG_WEIDMANN) {
                System.err.println(this.getErrors().toString());
            }
        }
        else { // if there were no errors so far, try to build an obligation
            ObligationCreator obligationCreator = new ObligationCreator(sp);
            this.setState(obligationCreator.buildObligation());
            this.language = obligationCreator.getLanguage();

            if(Globals.DEBUG_WEIDMANN) {
                if(!(this.getState() == null)) {
                    System.err.println("Obligation: " + this.getState().toString());
                }
            }
            // if we failed to build an obligation, store the errors that occured
            if (this.getState() == null && this.getErrors().isEmpty()) {
                List<ParseError> errorMessages = obligationCreator.getErrors();
                for(ParseError er : errorMessages) {
                    this.getErrors().add(er);
                }
                //this.type = ModedType.createModedInput(Language.SRS); // was: QTRS
                this.language = null;
                if(Globals.DEBUG_WEIDMANN) {
                    // System.err.flush();
                    System.err.println(this.getErrors().getFirst());
                }

            }

        }

        if(!this.getErrors().isEmpty() && Translator.logger.isLoggable(Level.SEVERE)) {
            Translator.logger.log(Level.SEVERE, this.getErrors().toString());
        }

    }

}
