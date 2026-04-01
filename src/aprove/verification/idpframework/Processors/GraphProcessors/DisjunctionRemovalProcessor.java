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
public class DisjunctionRemovalProcessor extends ItpfGraphProcessor {

    public DisjunctionRemovalProcessor() {
        super(new ItpfDisjunctionRemoval(), ApplicationMode.Multistep);
    }

    public DisjunctionRemovalProcessor(final ApplicationMode mode) {
        super(new ItpfDisjunctionRemoval(), mode);
    }

}
