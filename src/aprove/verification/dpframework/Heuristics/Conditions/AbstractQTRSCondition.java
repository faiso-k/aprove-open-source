package aprove.verification.dpframework.Heuristics.Conditions;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.Heuristics.*;
import aprove.verification.dpframework.TRSProblem.*;

public abstract class AbstractQTRSCondition implements Condition {

    @Override
    public boolean check(BasicObligation obl, Abortion aborter, RuntimeInformation rti) {
        return this.checkQTRS((QTRSProblem) obl, aborter);
    }
    public abstract boolean checkQTRS(QTRSProblem qtrs, Abortion aborter);

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (obl instanceof QTRSProblem) && this.isQTRSApplicable((QTRSProblem) obl);
    }
    public abstract boolean isQTRSApplicable(QTRSProblem qtrs);
}
