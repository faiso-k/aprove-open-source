package aprove.verification.oldframework.Bytecode.Processors.ToMCNP;

import java.math.*;

/**
 *
 * @author Matthias Hoelzel
 *
 */
public class PseudoMCSConstraint extends AbstractConstraint {
    public MCSVariable left;
    public MCSOperator op;
    public BigInteger right;

    /**
     * Constructor: [left] [op] [right]
     *
     * @param left MCSVariable
     * @param op relation symbol
     * @param right BigInteger
     */
    public PseudoMCSConstraint(final MCSVariable left, final MCSOperator op, final BigInteger right) {
        this.left = left;
        this.right = right;
        this.op = op;
    }

    @Override
    public String toString() {
        final String result = this.left.toString() + " " + this.op.toString() + " " + this.right.toString();
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.left == null) ? 0 : this.left.hashCode());
        result = prime * result + ((this.op == null) ? 0 : this.op.hashCode());
        result = prime * result + ((this.right == null) ? 0 : this.right.hashCode());
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final PseudoMCSConstraint other = (PseudoMCSConstraint) obj;
        if (this.left == null) {
            if (other.left != null) {
                return false;
            }
        } else if (!this.left.equals(other.left)) {
            return false;
        }
        if (this.op != other.op) {
            return false;
        }
        if (this.right == null) {
            if (other.right != null) {
                return false;
            }
        } else if (!this.right.equals(other.right)) {
            return false;
        }
        return true;
    }
}
