package aprove.verification.dpframework.IDPProblem.Processors.cgirp;

import aprove.verification.dpframework.IDPProblem.itpf.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public class ConditionalConstraint implements Immutable {

    public static ConditionalConstraint create(Itpf condition, Itpf constraint) {
        return new ConditionalConstraint(condition, constraint);
    }

    private final Itpf constraint;
    private final Itpf condition;

    public ConditionalConstraint(Itpf condition, Itpf constraint) {
        this.condition = condition;
        this.constraint = constraint;
    }

    public Itpf getConstraint() {
        return this.constraint;
    }

    public Itpf getCondition() {
        return this.condition;
    }


}
