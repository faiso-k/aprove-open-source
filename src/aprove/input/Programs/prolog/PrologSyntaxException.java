package aprove.input.Programs.prolog;

public class PrologSyntaxException extends RuntimeException {
    private static final long serialVersionUID = 3977345199810796279L;

    public PrologSyntaxException () {
        super("A syntax error occured on the given input!");
    }

    public PrologSyntaxException(String s) {
        super(s);
    }
}
