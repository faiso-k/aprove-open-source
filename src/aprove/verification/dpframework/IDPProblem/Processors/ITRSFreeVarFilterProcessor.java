package aprove.verification.dpframework.IDPProblem.Processors;

import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;

/**
 *
 * @author Martin Pluecker
 */
public class ITRSFreeVarFilterProcessor extends ITRSFilterProcessor {

    protected static final Arguments args;
    static {
        args = new Arguments();
        ITRSFreeVarFilterProcessor.args.filterHeuristic = new IdpFreeVarFilterHeuristic();
    }


    public ITRSFreeVarFilterProcessor() {
        super(ITRSFreeVarFilterProcessor.args);
    }

}
