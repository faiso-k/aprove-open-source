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
public class VarReductProcessor extends ItpfGraphProcessor {

    public VarReductProcessor() {
        super(new ItpfVarReduct(), ApplicationMode.Multistep);
    }

    public VarReductProcessor(final ApplicationMode mode) {
        super(new ItpfVarReduct(), mode);
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        if (this.applicationMode != ApplicationMode.Multistep) {
            return false;
        }
        if (mark.getClass() == this.getClass()) {
            return true;
        }
        if (mark.getClass() == RelOpProcessor.class) {
            return true;
        }
        if (mark.getClass() == VarReductProcessor.class) {
            return true;
        }
        return false;
    }

}
