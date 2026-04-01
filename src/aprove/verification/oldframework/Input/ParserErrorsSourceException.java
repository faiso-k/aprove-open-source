package aprove.verification.oldframework.Input;

import aprove.input.Utility.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * Thrown when a parser is not able to work correctly on given input.
 *   @author Martin Mertens
 *   @version $Id$
 */

public class ParserErrorsSourceException extends SourceException {

    private ParseErrors errors;
    private Input input;

    public ParserErrorsSourceException(ParseErrors errors, Proof proof, Input input) {
        super("Parser Errors Source Exception", proof, input.getName());
        this.errors = errors;
        this.input = input;
    }

    public ParserErrorsSourceException(ParseErrors errors, Input input) {
        super("Parser Errors Source Exception",new ParserErrorsSourceExceptionProof(errors,input),input.getName());
        this.errors = errors;
        this.input = input;
    }

    public Input getInput() {
        return this.input;
    }

    public ParseErrors getParseErrors() {
        return this.errors;
    }

    @Override
    public String getMessage() {
        return "Parsing " + this.input + " failed: " + this.errors;
    }

}
