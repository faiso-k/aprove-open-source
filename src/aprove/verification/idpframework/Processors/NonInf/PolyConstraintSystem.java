package aprove.verification.idpframework.Processors.NonInf;

import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;
import immutables.*;


/**
 *
 * @author MP
 */
public class PolyConstraintSystem<C extends SemiRing<C>> {

    private final ImmutableCollection<Polynomial<C>> constraints;

    private PolyConstraintSystem(final ImmutableCollection<Polynomial<C>> constraints) {
        this.constraints = constraints;
    }

    public ImmutableCollection<Polynomial<C>> getConstratins() {
        return this.constraints;
    }

}
