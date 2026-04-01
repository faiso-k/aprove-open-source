package aprove.verification.dpframework.IDPProblem.Processors.cgirp;

import aprove.verification.dpframework.IDPProblem.itpf.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public interface IPolynomialCCSolver {

    public ImmutableSet<ItpfItp> solve(Itpf conditionalConstraints);

}
