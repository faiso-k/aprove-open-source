package aprove.verification.dpframework.Heuristics.Conditions;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Processors.*;
import aprove.verification.dpframework.DPProblem.Processors.QDPUncurryingProcessor.*;

/**
 * QDPUncurryingCondition.<p>
 * Its check returns <code>true</code> iff the
 * QDPUncurryingProcessor is applicable.<p>
 *
 * Created: May 25, 2011
 *
 * @author Carsten Fuhs
 */

public class QDPUncurryingCondition extends AbstractQDPCondition {

    private final UncurryMethod method;

    private final boolean top;

    @ParamsViaArgumentObject
    public QDPUncurryingCondition(final Arguments arguments) {
        this.method = arguments.method;
        this.top = arguments.top;
    }

    public static class Arguments {
        /** Use the first technique that was implemented as default **/
        public UncurryMethod method = UncurryMethod.HIRO_MIDDEL_ZANKL;

        public boolean top = false;
    }

    @Override
    public boolean checkQDP(QDPProblem qdp, Abortion aborter) {
        boolean result = QDPUncurryingProcessor.isUncurryingApplicable(qdp,
                this.method, this.top).x;
        return result;
    }

    @Override
    public boolean isQDPApplicable(QDPProblem qdp) {
        return true;
    }
}
