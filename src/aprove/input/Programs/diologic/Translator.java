package aprove.input.Programs.diologic;

import java.io.*;

import aprove.*;
import aprove.input.Generated.diologic.lexer.*;
import aprove.input.Generated.diologic.node.*;
import aprove.input.Generated.diologic.parser.*;
import aprove.input.Utility.*;
import aprove.verification.oldframework.Input.*;

/**
 * Translator can be used to translate a diophantine logic formula into the
 * corresponding internal representation.
 * @author weidmann
 * @version $Id$
 */
public class Translator extends aprove.verification.oldframework.Input.Translator.TranslatorSkeleton {

    /**
     * Main method only for testing and debugging!
     * @param args Ignored.
     */
    public static void main(String[] args){
        Translator tr = new Translator();
        try {

            String[] dir = {"ValidAtomicFormulae","InvalidAtomicFormulae",
                    "ValidNonAtomicFormulae","InvalidNonAtomicFormulae", "whatever", "demo"};
            String directory = dir[5];
            String filename = "/home/weidmann/dio/" + directory + "/1.dio";
            File f = new File(filename);
            int i = 1;
            while(f.exists()){

                System.err.println("\n*** EXAMPLE "+i + ": ***");
                tr = new Translator();

                tr.translate(new File(filename));
                i++;
                System.err.println();
                filename = "/home/weidmann/dio/" + directory + "/"+i+".dio";
                f = new File(filename);
            }
        }
        catch (Exception e) {
           System.err.println(tr.getErrors().toString());
           System.err.println(e);
           e.printStackTrace();
        }
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Input.Translator#getLanguage()
     */
    @Override
    public Language getLanguage() {
        // ModedType set arbitrarily to SRS
        return Language.SRS;
    }


    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Input.Translator#translate(java.io.Reader)
     */
    @Override
    public void translate(Reader reader) {
        this.setState(null);
        OnePass op = null;
        try {
            Lexer lexer = new Lexer(new PushbackReader(reader,1024));
            Parser parser = new Parser(lexer);
            Start tree = parser.parse();

            op = new  OnePass();
            tree.apply(op);
        }
        catch (Exception e) {
            ParseError pe = new ParseError(ParseError.ERROR);
            if (e instanceof ParserException) {
                Token t = ((ParserException) e).getToken();
                pe.setToken(t.toString().trim());
                pe.setPosition(t.getLine(), t.getPos());
                pe.setMessage("Error parsing input: " + e.getMessage());
            }
            else if (e instanceof ParseException) {
                Token t = ((ParseException) e).getToken();
                if (t != null) {
                    pe.setToken(t.toString().trim());
                    pe.setPosition(t.getLine(), t.getPos());
                }
                pe.setMessage("Parse error: " + e.getMessage());
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

        if (!this.getErrors().isEmpty()) // if there were errors so far
        {
            this.setState(null);

            if (Globals.DEBUG_WEIDMANN) {
                System.err.println(this.getErrors().toString());
            }
        }
        else { // if there were no errors so far
            System.err.println("Formula:");
            if (op.getFormula() != null) {
                System.err.println(op.getFormula().toString());
            }

            this.setState(null);
        }

        /* if(!this.errors.isEmpty() && logger.isLoggable(Level.SEVERE)) {
            logger.log(Level.SEVERE, this.errors.toString());
        }*/

    }

}
