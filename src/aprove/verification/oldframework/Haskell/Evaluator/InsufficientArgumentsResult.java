package aprove.verification.oldframework.Haskell.Evaluator;

import aprove.verification.oldframework.Haskell.*;

/**
 * An error indicating that a function was called
 * with too few arguments.
 *
 * @author matraf
 *
 * @version $Id$
 */
public class InsufficientArgumentsResult extends ErrorResult {

    public InsufficientArgumentsResult(ErrorType errorType, HaskellObject errStr, int errorFrameNumber) {
        super(errorType, errStr, errorFrameNumber);
    }

}
