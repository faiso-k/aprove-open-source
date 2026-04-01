/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

public class OPCLogVar<C extends GPolyCoeff> implements OrderPolyConstraint<C> {

    private final String name;

    public OPCLogVar(String name) {
        this.name = name;
    }

    @Override
    public Set<GPolyVar> getFreeVariables() {
        return Collections.<GPolyVar>emptySet();
    }

    @Override
    public boolean isClosed() {
        return true;
    }

    @Override
    public OrderPolyConstraint<C> visit(ConstraintVisitor<C> v) {
        v.fcaseLogVar(this);
        return v.caseLogVar(this);
    }

    public String getName() {
        return this.name;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        } else {
            if (other instanceof OPCLogVar) {
                return this.name.equals(((OPCLogVar)other).getName());
            } else {
                return false;
            }
        }
    }

    @Override
    public int hashCode() {
        return this.name.hashCode();
    }

    @Override
    public String toString() {
        return this.name;
    }

}
