package aprove.verification.dpframework.PATRSProblem.Processors;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.PATRSProblem.*;

/**
 * Processor that prints a converted ITRS.  Features not supported by ITRS are ignored!
 *
 * @author Stephan Falke
 * @version $Id$
 */
@NoParams
public class PATRSToITRSProcessor extends PATRSProcessor {

    @Override
    protected Result processPATRS(PATRSProblem patrs, Abortion aborter) throws AbortionException {
        System.out.println(patrs.toITRSString());
        return ResultFactory.unsuccessful();
    }

}
