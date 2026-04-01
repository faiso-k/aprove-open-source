package aprove.input.Terms.term;

import java.io.*;
import java.util.*;

import aprove.input.Generated.term.lexer.*;
import aprove.input.Generated.term.node.*;
import aprove.input.Generated.term.parser.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Syntax.*;

/** This class is the interface to the TERM parser.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public class Translator extends TermTranslator {

    @Override
    public void translate(Reader reader) throws TranslationException {
    if (this.context == null) {
        throw new TranslationException(
                new SourceNotInitializedException("TERM requires Program as context"));
    }
    Set prefixIds = new HashSet();
    Set infixIds = new HashSet();
    Iterator it = this.context.getFunctionSymbols().iterator();
    while (it.hasNext()) {
        SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol)it.next();
        String name = fsym.getName();
        if (fsym.isInfix()) {
        infixIds.add(name);
        }
        else {
        prefixIds.add(name);
        }
    }
    try {
        this.translate(new Parser(new TermLexer(new PushbackReader(reader, 1024), prefixIds, infixIds)).parse());
    } catch (ParserException e) {
        throw new TranslationException(e);
    } catch (LexerException e) {
        throw new TranslationException(e);
    } catch (IOException e) {
        throw new TranslationException(e);
    }
    }

    public void translate(Start tree) throws ParserException {
    TransformPass tp = new TransformPass();
    tp.setContext(this.context);
    tree.apply(tp);
    Pass1 p = new Pass1();
    p.setContext(this.context);
    tree.apply(p);
    p.checkErrors();
    this.term = p.getTerm();
    }

    @Override
    public Language getLanguage() {
        return Language.TERM;
    }

}
