/**
 *
 * @author mpluecke
 * @version $Id$
 */

package aprove.verification.idpframework.Processors.GraphProcessors;

import aprove.strategies.Annotations.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;

@NoParams
public class RelOpProcessor extends ItpfGraphProcessor {

    public RelOpProcessor() {
        super(new ItpfRelOp(), ApplicationMode.Multistep);
    }

    public RelOpProcessor(final ApplicationMode mode) {
        super(new ItpfRelOp(), mode);
    }

}
