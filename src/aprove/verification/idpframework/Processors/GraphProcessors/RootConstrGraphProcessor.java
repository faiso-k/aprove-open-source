/**
 *
 * @author mpluecke
 * @version $Id$
 */

package aprove.verification.idpframework.Processors.GraphProcessors;

import aprove.strategies.Annotations.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;

@NoParams
public class RootConstrGraphProcessor extends ItpfGraphProcessor {

    public RootConstrGraphProcessor() {
        super(null, ApplicationMode.Multistep);
    }

    public RootConstrGraphProcessor(final ApplicationMode mode) {
        super(null, mode);
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return false;
    }

}
