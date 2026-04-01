package aprove.input.Utility;

public class UnhandledConstructException extends UnsupportedOperationException {
    public UnhandledConstructException(String construct) {
        super("Don't know how to handle " + construct + ".");
    }
}
