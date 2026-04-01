/**
 *
 * @author mpluecke
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.Processors;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.cap.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.itpf.rules.*;

@NoParams
public class ICapGraphProcessor extends ItpfGraphProcessor {

    public ICapGraphProcessor() {
        super(new ItpfCap(IECap.Estimation.getEstimation(IECap.Estimation.DEFAULT)), IItpfRule.ApplicationMode.Multistep);
    }

    public ICapGraphProcessor(IECap.Estimation estimation, IItpfRule.ApplicationMode mode) {
        super(new ItpfCap(IECap.Estimation.getEstimation(estimation)), mode);

    }

}
