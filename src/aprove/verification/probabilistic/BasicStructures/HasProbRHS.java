package aprove.verification.probabilistic.BasicStructures;

import aprove.verification.dpframework.BasicStructures.*;

/**
 * Objects that have a Multidistribution as rhs, where the elements are terms.
 *
 * @author Jan-Christoph Kassing
 * @version $Id$
 */
public interface HasProbRHS {

    /**
     * give right hand side of this. Must return non-null value.
     */
    public MultiDistribution<? extends TRSTerm> getRight();

}
