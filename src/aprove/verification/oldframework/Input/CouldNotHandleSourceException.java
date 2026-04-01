package aprove.verification.oldframework.Input;

import aprove.verification.theoremprover.TerminationProofs.*;

/**
 *   @author swiste
 *   @version $Id$
 */

public class CouldNotHandleSourceException extends SourceException {

    public CouldNotHandleSourceException(String message, Input input) {
        super(message,new CouldNotHandleSourceExceptionProof(message,input),input.getName());
    }

}
