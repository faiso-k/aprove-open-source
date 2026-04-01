package aprove.verification.dpframework.Orders.Solvers;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.Orders.*;

/**
 * Interface for solvers for Constraint<T> which can handle Abortions.
 *
 * @param <T>
 */
public interface AbortableConstraintSolver<T> {

    public ExportableOrder<T> solve(Collection<Constraint<T>> cs, Abortion aborter) throws AbortionException;

}
