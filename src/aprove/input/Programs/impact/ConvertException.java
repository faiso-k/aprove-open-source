package aprove.input.Programs.impact;


public class ConvertException extends RuntimeException {

    public ConvertException(final int line, final int pos, final String message) {
        super("[" + String.valueOf(line) + "," + String.valueOf(pos) + "] " + message);
    }
}
