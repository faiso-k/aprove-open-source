package aprove.input.Programs.intTrs;

import java.io.*;

import org.antlr.runtime.*;

import aprove.input.Generated.IntTRS.*;
import aprove.input.Utility.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Translator.*;
import aprove.verification.oldframework.IntTRS.*;

public class Translator extends TranslatorSkeleton {

    private final Language language = Language.INTTRS;

    @Override
    public Language getLanguage() {
        return this.language;
    }

    @Override
    public void translate(final Reader reader) {
        try {
            final IntTRSLexer lex = new IntTRSLexer(new ANTLRReaderStream(reader));
            final CommonTokenStream tokens = new CommonTokenStream(lex);
            final IntTRSParser parser = new IntTRSParser(tokens);
            final IRSwTProblem intTrs = parser.intTRS();

            this.setState(intTrs);
        } catch (final RecognitionException re) {
            final ParseError pe = new ParseError();
            pe.setLine(re.line);
            pe.setColumn(re.charPositionInLine);
            pe.setMessage(re.getMessage());
            this.getErrors().add(pe);
        } catch (final IOException e) {
            final ParseError pe = new ParseError();
            pe.setMessage(e.getMessage());
            this.getErrors().add(pe);
        }
    }

}
