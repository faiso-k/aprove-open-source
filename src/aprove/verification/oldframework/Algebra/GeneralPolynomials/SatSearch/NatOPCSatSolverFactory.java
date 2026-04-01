/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.LogOPCSolver.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.NatOPCSatSolver.*;

public class NatOPCSatSolverFactory implements LogOPCSolverFactory<BigIntImmutable> {

    private final Arguments arguments;

    @ParamsViaArgumentObject
    public NatOPCSatSolverFactory(Arguments arguments) {
        this.arguments = arguments;
    }

    @Override
    public LogOPCSolver<BigIntImmutable> newSolver() {
        return new NatOPCSatSolver(this.arguments);
    }

}

