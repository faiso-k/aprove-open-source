/**
 *
 * @author mpluecke
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.Processors;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.itpf.rules.*;

@NoParams
public class RootConstrGraphProcessor extends ItpfGraphProcessor {

    public RootConstrGraphProcessor() {
        super(new ItpfRootConstr(), IItpfRule.ApplicationMode.Multistep);
    }

    public RootConstrGraphProcessor(IItpfRule.ApplicationMode mode) {
        super(new ItpfRootConstr(), mode);
    }

}
