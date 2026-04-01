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
public class RootConstrProcessor extends ItpfGraphProcessor {

    public RootConstrProcessor() {
        super(new ItpfRootConstr(), ApplicationMode.Multistep);
    }

    public RootConstrProcessor(final ApplicationMode mode) {
        super(new ItpfRootConstr(), mode);
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return false;
    }

}
