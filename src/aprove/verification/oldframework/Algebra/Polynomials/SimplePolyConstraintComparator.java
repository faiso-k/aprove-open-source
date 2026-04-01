package aprove.verification.oldframework.Algebra.Polynomials;

import java.util.*;

import immutables.*;

/**
 * @author Carsten Fuhs
 *
 * A Comparator which compares two SimplePolyConstraints based on the number
 * of addends of their SimplePolynomials.
 *
 * Note: this comparator imposes orderings that are inconsistent with equals.
 */
public class SimplePolyConstraintComparator implements Comparator<SimplePolyConstraint>, Immutable {

    /**
     * @param constraint1  the first of the two SimplePolyConstraints to be
     *  compared
     * @param constraint2  the second of the two SimplePolyConstraints to be
     *  compared
     * @return the difference between the number of addends of constraint2
     *  and constraint1
     */
    @Override
    public int compare(SimplePolyConstraint constraint1, SimplePolyConstraint constraint2) {
        return constraint2.numberOfAddends() - constraint1.numberOfAddends();
    }
}
