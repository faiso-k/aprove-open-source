package aprove.verification.dpframework.Heuristics.Conditions;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.Heuristics.*;
import aprove.verification.dpframework.IDPProblem.*;

public abstract class AbstractITRSCondition implements Condition {

    @Override
    public boolean check(final BasicObligation obl, final Abortion aborter, RuntimeInformation rti) {
        return this.checkITRS((ITRSProblem) obl, aborter);
    }

    public abstract boolean checkITRS(ITRSProblem itrs, Abortion aborter);

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return (obl instanceof ITRSProblem)
            && this.isITRSApplicable((ITRSProblem) obl);
    }

    public abstract boolean isITRSApplicable(ITRSProblem itrs);
}
