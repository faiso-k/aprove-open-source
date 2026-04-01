package aprove.input.Programs.t2;

import java.io.*;

import org.antlr.runtime.*;

import aprove.input.Generated.T2IntSys.*;
import aprove.input.Utility.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Translator.*;

public class Translator extends TranslatorSkeleton {

    private final Language language = Language.T2;

    @Override
    public Language getLanguage() {
        return this.language;
    }

    @Override
    public void translate(final Reader reader) {
        try {
            final T2IntSysLexer lex = new T2IntSysLexer(new ANTLRReaderStream(reader));
            final CommonTokenStream tokens = new CommonTokenStream(lex);
            final T2IntSysParser parser = new T2IntSysParser(tokens);
            final T2IntSys intSys = parser.t2IntSys();

            this.setState(intSys);
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
