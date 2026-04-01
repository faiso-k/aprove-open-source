package aprove.verification.dpframework.Orders.Solvers;

import java.util.*;

import aprove.verification.dpframework.Orders.*;

public interface ConstraintSolver<T> {

    public Order<T> solve(Collection<Constraint<T>> cs);

}
