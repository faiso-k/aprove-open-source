package aprove.input.Diophantine;

import java.io.*;

import aprove.*;
import aprove.input.Generated.diophantine.lexer.*;
import aprove.input.Generated.diophantine.node.*;
import aprove.input.Generated.diophantine.parser.*;
import aprove.input.Utility.*;
import aprove.verification.diophantine.*;
import aprove.verification.oldframework.Input.*;

/**
 * Translator can be used to translate a sets of diophantine constraints into the corresponding internal representation.
 * @author nowonder
 * @version $Id$
 */
public class Translator extends aprove.verification.oldframework.Input.Translator.TranslatorSkeleton {

    @Override
    public Language getLanguage() {
        return Language.DIOPHANTINE;
    }

    @Override
    public void translate(Reader reader) {
        this.setState(null);
        Pass p = new Pass();
        try {
            Lexer lexer = new Lexer(new PushbackReader(reader,1024));
            Parser parser = new Parser(lexer);
            Start tree = parser.parse();

            tree.apply(p);
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
        }

        this.setState(this.getErrors().isEmpty() ? new DiophantineConstraints(p.getContraints()) : null);
    }

}
