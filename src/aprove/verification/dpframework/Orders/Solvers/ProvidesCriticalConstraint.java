package aprove.verification.dpframework.Orders.Solvers;

import aprove.verification.dpframework.Orders.*;

/**
 * Interface for orders that supply a critical constraint on failure.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public interface ProvidesCriticalConstraint<T> {

    public Constraint<T> getCriticalConstraint();

}
