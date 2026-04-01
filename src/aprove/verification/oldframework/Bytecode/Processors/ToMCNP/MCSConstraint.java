package aprove.verification.oldframework.Bytecode.Processors.ToMCNP;

/**
 *
 * @author Matthias Hoelzel
 *
 */
public class MCSConstraint extends AbstractConstraint {
    public MCSVariable left, right;
    public MCSOperator op;

    /**
     * Constructor
     * @param leftVar left variable
     * @param sym relation symbol
     * @param rightVar right variable
     */
    public MCSConstraint(final MCSVariable leftVar, final MCSOperator sym, final MCSVariable rightVar) {
        this.left = leftVar;
        this.right = rightVar;
        this.op = sym;
    }

    @Override
    public String toString() {
        final String result = this.left.toString() + " " + this.op.toString() + " " + this.right.toString();
        return result;
    }

    @Override
    public boolean equals(final Object other) {
        if ((other == null) || !(other instanceof MCSConstraint)) {
            return false;
        } else {
            final MCSConstraint otherCon = (MCSConstraint) other;
            return this.left.equals(otherCon.left)
                && this.right.equals(otherCon.right)
                && this.op.equals(otherCon.op);
        }
    }

    @Override
    public int hashCode() {
        return this.left.hashCode() * 3 + this.right.hashCode() * 7 + this.op.hashCode() * 2;
    }

    /**
     * Checks whether or not [this] implies [other].
     * For example x = y implies x >= y.
     *
     * @param other a MCSConstraint
     * @return True iff other != null && [this] implies [other]
     */
    public boolean implies(final MCSConstraint other) {
        if (other == null) {
            return false;
        }

        final MCSConstraint thisNormalized = this.normalize();
        final MCSConstraint otherNormalized = other.normalize();

        if (thisNormalized.op.equals(MCSOperator.MCS_EQ)) {
            if (otherNormalized.op.equals(MCSOperator.MCS_EQ)
                    || otherNormalized.op.equals(MCSOperator.MCS_GE)) {
                return ((thisNormalized.left.equals(otherNormalized.left)
                         && thisNormalized.right.equals(otherNormalized.right))
                        || (thisNormalized.left.equals(otherNormalized.right)
                            && thisNormalized.right.equals(otherNormalized.left)));
            } else {
                return false;
            }
        } else if (thisNormalized.op.equals(MCSOperator.MCS_GE)) {
            return thisNormalized.equals(otherNormalized);
        } else if (thisNormalized.op.equals(MCSOperator.MCS_G)) {
            if (otherNormalized.op.equals(MCSOperator.MCS_G)
                    || otherNormalized.op.equals(MCSOperator.MCS_GE)) {
                return otherNormalized.left.equals(thisNormalized.left)
                       && otherNormalized.right.equals(thisNormalized.right);
            } else {
                return false;
            }
        } else {
            assert false;
            return false;
        }
    }

    /**
     * Turns y < x into x > y and y <= x into x >= y.
     * Constraints like x < y, x <= y, x = y will be untouched.
     *
     * @return normalized constraint.
     */
    public MCSConstraint normalize() {
        if (this.op.equals(MCSOperator.MCS_L)) {
            return new MCSConstraint(this.right, MCSOperator.MCS_G, this.left);
        }
        if (this.op.equals(MCSOperator.MCS_LE)) {
            return new MCSConstraint(this.right, MCSOperator.MCS_GE, this.left);
        }
        return this;
    }
}
