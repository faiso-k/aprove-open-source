/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * @author cotto
 */
public class NonCountingCircuitFactoryCreator implements FormulaFactoryCreator {

    /**
     * @return a _fresh_ FormulaFactory (NonCountingCircuitFactory).
     */
    @Override
    public FormulaFactory<None> getFactory() {
        return new NonCountingCircuitFactory<None>();
    }

}
