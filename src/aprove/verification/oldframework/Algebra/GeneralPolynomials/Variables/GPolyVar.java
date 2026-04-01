package aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import immutables.*;

/**
 * Variables implementing this interface can be used to hide inner variables
 * and still work with the current framework, including variable substitution.
 * For example "max(x, y)" can be a variable of the polynomial and the
 * substitution [x/y, y/x] on that variable gives "max(y, x)" as expected.
 * @author cotto
 * @version $Id$
 */
public interface GPolyVar extends Immutable, Exportable {
    /**
     * @param vars the variables to be replaced.
     * @return true iff some to-be-replaced variable is contained in this
     * object.
     */
    boolean isAffected(Collection<? extends GPolyVar> vars);

    /**
     * Replace the encapsulated variables according to the replacement map.
     * @param <A> the type of the coefficients.
     * @param <B> the type of the variables.
     * @param replacement the replacement map giving a polynomial for each
     * variable.
     * @return the polynomial which results of applying the substitution to
     * this.
     */
    <A extends GPolyCoeff, B extends GPolyVar> GPoly<A, B> replace(Map<B, ? extends GPoly<A, B>> replacement);

    /**
     * @return the variables name.
     */
    String getName();
}
