package aprove.verification.dpframework.Heuristics.Conditions;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.TRSProblem.*;

/**
 * Detects if a given QTRSProblem has a rule set which has
 * at least a certain cardinality.
 *
 * @author fuhs
 */
public class QTRSHighCardinalityCondition extends AbstractQTRSCondition {

    private final int size;

    @ParamsViaArgumentObject
    public QTRSHighCardinalityCondition(Arguments arguments) {
        this.size = arguments.size;
    }

    @Override
    public boolean checkQTRS(QTRSProblem qtrs, Abortion aborter) {
        final int qtrsCardinality = qtrs.getR().size();
        return this.size <= qtrsCardinality;
    }

    @Override
    public boolean isQTRSApplicable(QTRSProblem qtrs) {
        return true;
    }

    public static class Arguments {
        public int size = 400;
    }
}
