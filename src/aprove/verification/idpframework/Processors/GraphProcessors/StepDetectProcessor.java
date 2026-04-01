/**
 *
 * @author mpluecke
 * @version $Id$
 */

package aprove.verification.idpframework.Processors.GraphProcessors;

import aprove.strategies.Annotations.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;

@NoParams
public class StepDetectProcessor extends ItpfGraphProcessor {

    public StepDetectProcessor() {
        super(new ItpfStepDetect(), ApplicationMode.Multistep);
    }

    public StepDetectProcessor(final ApplicationMode mode) {
        super(new ItpfStepDetect(), mode);
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return false;
    }

}
