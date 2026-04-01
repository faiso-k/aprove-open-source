package aprove.verification.oldframework.Input;

import java.io.*;

import aprove.input.Utility.*;

/**
 * Interface for translators.
 *  <P>
 *  Implement by extending Translator.Skeleton, e.g.:<BR>
 *  <TT>public class MyTranslator extends Translator.Skeleton implements Translator { ... </TT>
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public interface Translator {

    /**
     * Abstract skeleton implementation of the Translator interface.
     */
    abstract class TranslatorSkeleton implements Translator {

        /**
         * The parse errors which occurred so far.
         */
        private ParseErrors errors;

        /**
         * The state of the translator (usually the program/problem to parse).
         */
        private Object state;

        /**
         * The proto-annotation. It enables the translator to decide whether to
         * construct, e.g., a CpxTrs or a Trs based on the information provided
         * by the proto-annotation. This possibility is used by the gui.
         */
        private String protoAnnotation = null;

        /**
         * Creates a new Translator with an empty list of parse errors.
         */
        public TranslatorSkeleton() {
            this.errors  = new ParseErrors();
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Input.Translator#getErrors()
         */
        @Override
        public ParseErrors getErrors() {
            return this.errors;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Input.Translator#getState()
         */
        @Override
        public Object getState() {
            return this.state;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Input.Translator#hasErrors()
         */
        @Override
        public boolean hasErrors() {
            return this.errors.getMaxLevel() >= ParseError.ERROR;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Input.Translator#setState(java.lang.Object)
         */
        @Override
        public void setState(Object state) {
            this.state = state;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Input.Translator#throwOnError()
         */
        @Override
        public void throwOnError() {
            this.errors.throwOnError();
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Input.Translator#translate(java.io.File)
         */
        @Override
        public void translate(File file) throws FileNotFoundException, TranslationException {
            this.translate(new InputStreamReader(new FileInputStream(file)));
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Input.Translator#translate(aprove.verification.oldframework.Input.Input)
         */
        @Override
        public void translate(Input input) throws TranslationException {
            this.translate(input.getContent());
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Input.Translator#translate(java.io.InputStream)
         */
        @Override
        public void translate(InputStream stream) throws TranslationException {
            this.translate(new InputStreamReader(stream));
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Input.Translator#translate(java.lang.String)
         */
        @Override
        public void translate(String input) throws TranslationException {
            this.translate(new StringReader(input));
        }

        /**
         * @param e The ParseErrors to set.
         */
        protected void setErrors(ParseErrors e) {
            this.errors = e;
        }

        @Override
        public void setProtoAnnotation(String annotation) {
            this.protoAnnotation = annotation;
        }

        @Override
        public String getProtoAnnotation() {
            return this.protoAnnotation;
        }
    }

    /**
     * @return The set of errors encountered during translation.
     */
    public ParseErrors getErrors();

    /**
     * @return The type of this Translator.
     */
    public Language getLanguage();

    /**
     * @return The current state of the Translator (usually the program/problem to parse).
     */
    public Object getState();

    /**
     * @return Whether there were any errors during translation.
     */
    public boolean hasErrors();

    /**
     * Sets the state of this translator.
     * @param state State that replaces the state of this translator.
     */
    public void setState(Object state);

    /**
     * TODO Is this method really useful?
     * Throw an error iff there were any errors during translation.
     * @throws RuntimeException If there were any errors during translation.
     */
    public void throwOnError() throws RuntimeException;

    /**
     * Translate using the given file as source.
     * @param file File to translate.
     * @throws FileNotFoundException If the file does not exist.
     * @throws TranslationException If any exception occurs during the parsing process.
     * @see File
     */
    public void translate(File file) throws FileNotFoundException, TranslationException;

    /**
     * Translate using the given input as source.
     * @param input Input to translate from.
     * @throws TranslationException If any exception occurs during the parsing process.
     * @see Reader
     */
    public void translate(Input input) throws TranslationException;

    /**
     * Translate using the given stream as source.
     * @param stream Stream to translate from.
     * @throws TranslationException If any exception occurs during the parsing process.
     * @see InputStream
     */
    public void translate(InputStream stream) throws TranslationException;

    /**
     * Translate using the given reader as source.
     * @param reader Reader to translate from.
     * @throws TranslationException If any exception occurs during the parsing process.
     * @see Reader
     */
    public void translate(Reader reader) throws TranslationException;

    /**
     * Translate using the given string as source.
     * @param input String input to translate.
     * @throws TranslationException If any exception occurs during the parsing process.
     * @see String
     */
    public void translate(String input) throws TranslationException;

    /** @see Translator.TranslatorSkeleton#protoAnnotation */
    public void setProtoAnnotation(String annotation);

    /** @see Translator.TranslatorSkeleton#protoAnnotation */
    public String getProtoAnnotation();
}
