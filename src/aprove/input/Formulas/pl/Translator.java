package aprove.input.Formulas.pl;

import java.io.*;
import java.util.*;

import aprove.*;
import aprove.input.Generated.pl.lexer.*;
import aprove.input.Generated.pl.node.*;
import aprove.input.Generated.pl.parser.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Syntax.*;

/** This class is the interface to the PL parser.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public class Translator extends FormulaTranslator {

    protected MainPass mainPass;

    public Translator() {
        this.mainPass = new MainPass();
    }

    @Override
    public void translate(Reader reader) throws TranslationException {

        if (this.context == null) {
            throw new TranslationException(
                    new SourceNotInitializedException("TERM requires Program as context"));
        }

        Set<String> prefixIds = new HashSet<String>();
        Set<String> infixIds = new HashSet<String>();
        infixIds.add(":");
        for (SyntacticFunctionSymbol functionSymbol : this.context.getFunctionSymbols()) {
            String name = functionSymbol.getName();
            if (functionSymbol.isInfix()) {
                infixIds.add(name);
            } else {
                prefixIds.add(name);
            }
        }

        FormulaLexer formulaLexer = new FormulaLexer(new PushbackReader(reader,1024), prefixIds, infixIds);
        Parser parser = new Parser(formulaLexer);
        Start start;
        try {
            start = parser.parse();
        } catch (ParserException e) {
            throw new TranslationException(e);
        } catch (LexerException e) {
            throw new TranslationException(e);
        } catch (IOException e) {
            throw new TranslationException(e);
        }

        this.translate(start);
    }

    protected void translate(Start tree) {

    try {
        TransformPass tp = new TransformPass();
        tp.setContext(this.context);
        tree.apply(tp);
        tp.getErrors().throwOnError();
        this.mainPass.setContext(this.context);
        tree.apply(this.mainPass);
    }
    catch (Exception e) {
        if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
            e.printStackTrace();
        }
    }
        this.mainPass.getErrors().throwOnError();
    }

    @Override
    public Formula getFormula() {
        return this.mainPass.getFormula();
    }

    @Override
    public Language getLanguage(){
        return Language.PL_FORMULA;
    }
}
