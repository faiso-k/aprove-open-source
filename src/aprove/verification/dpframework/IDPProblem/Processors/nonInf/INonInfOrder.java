/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.nonInf;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.orders.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.IConstraintGenerator.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;

public interface INonInfOrder extends IActiveOrder {

    public IDPGInterpretation getInterpretation();
    public IConstraintGeneratorProof getConstraintsProof();
    public boolean nonInf_lhsGEConst(GeneralizedRule rule);

}
