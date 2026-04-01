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
public class UnifyProcessor extends ItpfGraphProcessor {

    public UnifyProcessor() {
        super(new ItpfUnify(), ApplicationMode.Multistep);
    }

    public UnifyProcessor(final ApplicationMode mode) {
        super(new ItpfUnify(), mode);
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return false;
    }

}
