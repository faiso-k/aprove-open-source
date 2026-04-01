package aprove.verification.idpframework.Polynomials.Interpretation;

import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.*;
import aprove.verification.idpframework.Polynomials.*;
import immutables.*;

/**
 * @author MP
 */
public class VFICacheKey implements Immutable {

    public final Integer position;
    public final RelDependency relDependency;
    public final IActiveCondition activeCondition;
    private int hashCode;

    public VFICacheKey(final RelDependency relDependency,
            final IActiveCondition activeCondition, final Integer position) {
        this.relDependency = relDependency;
        this.activeCondition = activeCondition;
        this.position = position;
        {
            final int prime = 31;
            int result = 1;
            result = prime * result + relDependency.hashCode();
            result = prime * result + activeCondition.hashCode();
            result = prime * result + position.hashCode();
            this.hashCode = result;
        }
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

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
        final VFICacheKey other = (VFICacheKey) obj;
        return this.relDependency.equals(other.relDependency) && this.activeCondition.equals(other.activeCondition) && this.position.equals(other.position);
    }

}
