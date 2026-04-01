/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.nonInf;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

public class NonInfBound extends GAtomicVar {

    public NonInfBound() {
        super("Bound");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        return 235376532;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (!super.equals(obj)) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        return true;
    }

}
