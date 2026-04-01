package aprove.input.Programs.triples;

import java.io.*;

import aprove.verification.oldframework.Input.*;

/**
 * Translator for Dependency Triple Problems (uses Prolog Translator).
 * @author nowonder
 */
public class Translator extends aprove.verification.oldframework.Input.Translator.TranslatorSkeleton {

    aprove.input.Programs.prolog.Translator prologTrans =
            new aprove.input.Programs.prolog.Translator();

    @Override
    public Language getLanguage() {
        return Language.TRIPLES;
    }

    @Override
    public void translate(Reader reader) throws TranslationException {
        this.prologTrans.translateTriples(reader);
        this.setState(
            new TriplesProblem(this.prologTrans.getTriples(), this.prologTrans.getProgram(), this.prologTrans.getAfs())
        );
    }

}
