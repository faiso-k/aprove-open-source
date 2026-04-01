/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import immutables.*;

/**
 * A quantified constraint. The type (universal or existential) is open, which
 * is why this is an abstract class.
 * @author cotto
 * @param <C> The type of the coefficients inside the constraint.
 */
public abstract class OPCQuantifier<C extends GPolyCoeff>
    implements OrderPolyConstraint<C>, Immutable {
    /**
     * The constraint over that the quantifier stretches.
     */
    private final OrderPolyConstraint<C> constraint;

    /**
     * Cache the hashCode, because recursive computation is quite expensive.
     */
    private int hashCode = 0;

    /**
     * The variables covered by the quantifier.
     */
    private final ImmutableSet<GPolyVar> variables;

    /**
     * @param constraintParam The constraint over that the quantifier stretches.
     * @param variablesParam The variables covered by the quantifier.
     */
    public OPCQuantifier(final OrderPolyConstraint<C> constraintParam,
            final Set<GPolyVar> variablesParam) {
        this.constraint = constraintParam;
        this.variables = ImmutableCreator.create(variablesParam);
    }

    /**
     * @return the variables that are quantified by this quantifier.
     */
    public Set<GPolyVar> getQuantifiedVariables() {
        return this.variables;
    }

    /**
     * @return the constraint which is subject to this quantifier.
     */
    public OrderPolyConstraint<C> getInnerConstraint() {
        return this.constraint;
    }

    /**
     * @return true iff all free variables inside the constraint are covered by
     * this quantifier.
     */
    @Override
    public boolean isClosed() {
        return this.variables.containsAll(this.constraint.getFreeVariables());
    }

    /**
     * @return the set of all free variables in the constraint that are not
     * covered by this quantifier.
     */
    @Override
    public Set<GPolyVar> getFreeVariables() {
        Set<GPolyVar> temp =
            new LinkedHashSet<GPolyVar>(this.constraint.getFreeVariables());
        temp.removeAll(this.variables);
        return temp;
    }

    /**
     * @return the variables that are bound by the quantifier.
     * @return
     */
    protected ImmutableSet<GPolyVar> getVariables() {
        return this.variables;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        if (this.hashCode == 0) {
            final int prime = 31;
            int result = 1;
            result = prime * result + this.constraint.hashCode();
            result = prime * result + this.variables.hashCode();
            this.hashCode = result;
        }
        return this.hashCode;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    @SuppressWarnings("unchecked")
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final OPCQuantifier other = (OPCQuantifier) obj;
        if (this.constraint == null) {
            if (other.constraint != null) {
                return false;
            }
        } else if (!this.constraint.equals(other.constraint)) {
            return false;
        }
        if (this.variables == null) {
            if (other.variables != null) {
                return false;
            }
        } else if (!this.variables.equals(other.variables)) {
            return false;
        }
        return true;
    }
}
