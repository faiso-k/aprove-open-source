package aprove.strategies.Util;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;

/**
 * MultiProcessor framework. Processors implementing this interface can calculate different results for the
 * same input system and then merge these results, thus keeping results, that are thrown away by using many
 * different processors within an Any.
 *
 * The processSub() method has to contain the work. All jobs are run concurrently.
 *
 * The merge() method merges all available results.
 *
 * Every class implementing this interface should use an instance of {@link MultiProcessorHelper} to access
 * the framework.
 *
 * For an example implementation, see {@link aprove.verification.dpframework.TRSProblem.Processors.QTRSMultiRRRProcessor}.
 *
 * @author Karsten Behrmann
 */
public interface MultiProcessor<ProblemType extends BasicObligation, SubResultType> {
    public SubResultType processSub(int runnerNumber, ProblemType problem,
            Abortion aborter) throws AbortionException;

    public Result merge(ProblemType bObl, List<SubResultType> subResults, Abortion aborter) throws AbortionException;

    public String getName();
}
