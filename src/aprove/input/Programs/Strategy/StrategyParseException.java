package aprove.input.Programs.Strategy;

import java.io.*;

import org.antlr.runtime.*;

/**
 * Thrown by the strategy parser to indicate something went wrong.
 * Most callers will not care to catch this, but if they do want to,
 * this class should allow them to produce better errors.
 *
 * For all instances, either getParserError() or getIoError() will be non-null,
 * the other null.
 */
public class StrategyParseException extends RuntimeException {
    private static final long serialVersionUID = 1L;
    private final RecognitionException parserError;
    private final IOException ioError;

    public StrategyParseException(RecognitionException e, BaseRecognizer recognizer) {
        super(StrategyParseException.humanMessage(e, recognizer));
        this.parserError = e;
        this.ioError = null;
    }

    public StrategyParseException(IOException e) {
        super(e);
        this.parserError = null;
        this.ioError = e;
    }

    /* Blatantly stolen from BaseRecognizer.displayRecognitionError() */
    private static String humanMessage(RecognitionException e,
            BaseRecognizer recognizer) {
        String source = recognizer.getSourceName();
        if (source == null) {
            source = "<unknown>";
        }
        String message = recognizer.getErrorMessage(e, recognizer.getTokenNames());

        return source+", line "+e.line+" col "+e.charPositionInLine+": "+message;
    }

    /**
     * If this was thrown due to an error in the parser, returns that error.
     */
    public RecognitionException getParserError() {
        return this.parserError;
    }

    /**
     * If an IOException occurred that caused us to be thrown, returns that
     */
    public IOException getIoError() {
        return this.ioError;
    }
}
