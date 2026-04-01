/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * This interface takes care that each processor run gets a fresh factory.
 * Without this wrapper the factory would only be created once and its caches
 * would grow without limit.
 * @author cotto
 */

public interface FormulaFactoryCreator {
    /**
     * @return the factory, but always return a fresh instance.
     */
    FormulaFactory<None> getFactory();
}
