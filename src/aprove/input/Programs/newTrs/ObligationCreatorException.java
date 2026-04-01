package aprove.input.Programs.newTrs;

import java.util.*;

import aprove.input.Utility.*;

public class ObligationCreatorException extends Exception {

    private final List<ParseError> obligationErrors;

    public ObligationCreatorException(List<ParseError> obligationErrors) {
        this.obligationErrors = obligationErrors;
    }

    @Override
    public String getMessage() {
        return this.obligationErrors.toString();
    }

    public List<ParseError> getParseErrors() {
        return this.obligationErrors;
    }

}
