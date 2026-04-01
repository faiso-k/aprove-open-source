package aprove.input.Programs.xtc;

import java.io.*;

import org.xml.sax.*;

import aprove.input.Programs.newTrs.*;
import aprove.input.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Translator.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Translator for XML and XTC files.
 * @author unknown
 * @version $Id$
 */
public class Translator extends TranslatorSkeleton {

    /**
     * The language parsed by this translator (depends on the particular input).
     */
    private Language language;

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Input.Translator#getLanguage()
     */
    @Override
    public Language getLanguage() {
        return this.language;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Input.Translator#translate(java.io.Reader)
     */
    @Override
    public void translate(Reader reader) {
        InputSource is = new InputSource(reader);
        XTCParser xp = new XTCParser();
        try {
            Pair<BasicObligation, Language> p = xp.parse(is);
            this.setState(p.x);
            this.language = p.y;
        } catch (ParserError pe) {
            ParseError e = new ParseError();
            Locator l = pe.getLocator();
            e.setLine(l.getLineNumber());
            e.setColumn(l.getColumnNumber());
            e.setMessage(pe.getMessage());
            this.getErrors().add(e);
        } catch (ObligationCreatorException e) {
            this.getErrors().addAll(e.getParseErrors());
        }
    }

}
