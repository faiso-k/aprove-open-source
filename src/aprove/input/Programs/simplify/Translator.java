package aprove.input.Programs.simplify;

import java.io.*;

import aprove.input.Generated.simplify.lexer.*;
import aprove.input.Generated.simplify.node.*;
import aprove.input.Generated.simplify.parser.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Logic.FOFormulas.*;

/**
 * Program translator for simplify input
 * @author Andreas Kelle-Emden
 */
public class Translator extends ProgramTranslator {

    FOFormulaSet formulas = null;

    @Override
    public void translate(Reader reader) throws TranslationException {
        Start tree;
        Lexer lexer = new Lexer(new PushbackReader(reader, 1024));
        Parser parser = new Parser(lexer);
        try {
            tree = parser.parse();
        } catch (ParserException e) {
            throw new TranslationException(e);
        } catch (LexerException e) {
            throw new TranslationException(e);
        } catch (IOException e) {
            throw new TranslationException(e);
        }
        this.translate(tree);
    }

    public void translate(Start tree) {
        PassOne pass = new PassOne();
        tree.apply(pass);
        this.formulas = pass.getFormulaSet();
    }

    public FOFormulaSet getFormulaSet() {
        return this.formulas;
    }

    @Override
    public Language getLanguage() {
        return Language.SIMPLIFY;
    }

}
