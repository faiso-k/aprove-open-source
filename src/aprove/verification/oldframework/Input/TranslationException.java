package aprove.verification.oldframework.Input;

/**
 * Exception occured during a {@link Translator} run.
 *
 * <p>Most commonly used to wrap ParserExceptions, LexerExceptions,
 * IOExceptions</p>.
 */
public class TranslationException extends Exception {

    private static final long serialVersionUID = 1L;

    public TranslationException(String msg) {
        super(msg);
    }

    public TranslationException(Exception e) {
        super(e);
    }

    public TranslationException(String msg, Exception e) {
        super(msg, e);
    }
}
