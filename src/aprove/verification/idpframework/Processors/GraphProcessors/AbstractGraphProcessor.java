/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Processors.GraphProcessors;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Processors.*;

@NoParams
public abstract class AbstractGraphProcessor<ResultType extends Result, ProblemType extends IDPProblem> extends IDPProcessor<ResultType, ProblemType> {

    protected AbstractGraphProcessor(final String description) {
        super(description);
    }

}
