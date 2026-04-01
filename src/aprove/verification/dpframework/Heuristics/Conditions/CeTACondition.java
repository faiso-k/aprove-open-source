package aprove.verification.dpframework.Heuristics.Conditions;

import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.Heuristics.*;


/**
 * CeTACondition.<p>
 * Checks whether Options.certifier.isCeTA() is true<p>
 */
public class CeTACondition implements Condition {

    @Override
    public boolean check(final BasicObligation obl, final Abortion aborter, final RuntimeInformation rti) {
        return Options.certifier.isCeta();
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return true;
    }
}
