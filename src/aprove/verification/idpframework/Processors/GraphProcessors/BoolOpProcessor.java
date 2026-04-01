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
public class BoolOpProcessor extends ItpfGraphProcessor {

    public BoolOpProcessor() {
        super(new ItpfBoolOp(), ApplicationMode.Multistep);
    }

    public BoolOpProcessor(final ApplicationMode mode) {
        super(new ItpfBoolOp(), mode);
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
